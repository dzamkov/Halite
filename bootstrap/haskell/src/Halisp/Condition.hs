{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module Halisp.Condition (
	Formula (..),
	Term (..),
	Constraint (..),
	Condition,
	always,
	never,
	isAlways,
	isNever,
	simple,
	simples,
	solution,
	solutionFromList,
	map,
	sub,
	exists,
	existsFromList,
	existsRight,
	existsRightFromList,
	existsRightInt,
	conjunction,
	disjunction,
	(&&^),
	(||^),
	(==^),
	bind,
	extract,
	extractToList,
	isSolvable
) where

import Prelude hiding (map, fmap)
import Halisp.Volume (Volume)
import qualified Halisp.Volume as Volume
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List
import Data.Maybe (fromJust)
import Debug.Trace (trace)

-- Identifies a type constructor for a formula, which includes both terms and constraints.
class Formula f where

	-- Determines whether the given formula refers to (or depends on) any variable for
	-- which the given predicate returns true.
	frefers :: (Ord v) => (v -> Bool) -> f v -> Bool
	
	-- Applies a one-to-one mapping to the variables in a formula.
	fmap :: (Ord v, Ord n) => (v -> n) -> f v -> f n
	
-- Identifies a type constructor for a term.
class (Formula t) => Term r t where

	-- Constructs a term for a variable.
	tvar :: (Ord v) => r -> v -> t v

	-- Applies a substitution to the variables in a term.
	tsub :: (Ord v, Ord n) => r -> (v -> t n) -> t v -> t n
	
-- Applies a substitution map to a term.
tsubMap :: (Ord v, Term r t) => r -> Map v (t v) -> t v -> t v
tsubMap context subs = tsub context (\v -> maybe (tvar context v) id $ Map.lookup v subs)

-- Applies a substitution to a single variable in a term.
tsubOne :: (Ord v, Term r t) => r -> v -> t v -> t v -> t v
tsubOne context var target = tsub context (\v ->
	if v == var then target else tvar context v)
	
class (Formula k, Term r t) => Constraint r k t where
	
	-- Applies a substitution to the variables in a constraint.
	csub :: (Ord v, Ord n) => r -> (v -> t n) -> k v -> Condition k t n
	
	-- Gets a condition that is satisfied when the two given terms are equal
	-- (indistinguishable inside constraints).
	ceq :: (Ord v) => r -> t v -> t v -> Condition k t v
	
-- Applies a substitution map to a constraint.
csubMap :: (Ord v, Constraint r k t) => r -> Map v (t v) -> k v -> Condition k t v
csubMap context subs = csub context (\v -> maybe (tvar context v) id $ Map.lookup v subs)

-- Applies a substitution to a single variable in a constraint.
csubOne :: (Ord v, Constraint r k t) => r -> v -> t v -> k v -> Condition k t v
csubOne context var target = csub context (\v ->
	if v == var then target else tvar context v)
	
-- A boolean formula (including conjunctions and disjunctions, but lacking negation)
-- relating constraints.
data Condition k t v = Condition {

	-- The index of the next unused free variable in a condition. Free variables appear
	-- as "Right" variables in constraints and substitutions.
	degree :: Int,

	-- A volume representing the cases covered by a condition. The condition is satisifed
	-- in some sub-volume of this volume if all rules that intersect that sub-volume are
	-- satisfied.
	volume :: Volume,
	
	-- The rules (substitutions and constraints) for this volume, associated with the
	-- volumes they affect.
	rules :: [(Volume, Map v (t (Either v Int)), [k (Either v Int)])] }
	
deriving instance (Show v, Show (t (Either v Int)), Show (k (Either v Int)))
	=> Show (Condition k t v)

-- TODO: Prevent overflow of existential variables. 'degree' should not grow without
-- bound.

-- VOCAB: a rule is a constraint or substitution. A constraint is some restriction on the
-- values of variables (which stand in for terms). A substitution is an assignment of a
-- variable to a term. 

-- Rules for condition normalization:
-- 1. If a substitution intersects another rule, that rule must not refer to the variable
--    assigned in the substitution.
-- 2. The volume for a rule may not be empty.
-- 3. For any volume in a condition, there must not exist another volume whose contained
--    rules are a proper subset of the first volume's.
-- 4. Every entry in 'rules' must have a substitution or a constraint (no empty).

-- Optimizes the internal volumes of a condition.
optimize :: Condition k t v -> Condition k t v
optimize cond = res where
	volumes = List.map (\(v, _, _) -> v) $ rules cond
	(nVolume, proj) = Volume.optimize (volume cond) volumes
	res = Condition {
		degree = degree cond, volume = nVolume,
		rules = List.map (\(v, s, c) -> (proj v, s, c)) $ rules cond }

-- Inserts a set of rules (all associated with the same volume) into a rule set while
-- preserving normalization rules 1, 2 and 4. The given rules must all be independent (not
-- refer to any variable assigned in a given substitution). Note that some conflicts 
-- during insertion can only be resolved by applying a condition, which are returned along
-- with the rules.
insertRules :: (Ord v, Constraint r k t) => r
	-> [(Volume, Map v (t v), [k v], Condition k t v)]
	-> (Volume, Map v (t v), [k v])
	-> [(Volume, Map v (t v), [k v], Condition k t v)]
insertRules context rules part@(sVolume, sSubs, sCons) = res where
	memberOf map val = Map.member val map
	checkRules accum@(rules, parts) (oVolume, oSubs, oCons, oCond) = res where
		eVolume = Volume.intersection oVolume sVolume
		doVolume = Volume.difference oVolume eVolume
		commonSubs = Map.intersectionWith (ceq context) sSubs oSubs
		eConds'' = Map.elems commonSubs
		usSubs = Map.difference sSubs commonSubs
		(ioSubs, doSubs) = Map.partition (frefers $ memberOf usSubs) oSubs
		(isSubs, dsSubs) = Map.partition (frefers $ memberOf oSubs) usSubs
		insertSub (subs, conds) var value = res where
			nValue = tsubMap context subs value
			nSubs = Map.insert var nValue $ Map.map (tsubOne context var nValue) subs
			nConds = ceq context (tvar context var) nValue : conds
			res = if frefers (== var) nValue then (subs, nConds) else (nSubs, conds)
		(eSubs', eConds') = Map.foldlWithKey insertSub (doSubs, eConds'') dsSubs
		eSubs = Map.map (tsubMap context (Map.unionWith undefined ioSubs isSubs)) eSubs'
		(ioCons, doCons) = List.partition (frefers $ memberOf usSubs) oCons
		dsCons = List.filter (frefers $ memberOf oSubs) sCons
		eConds = List.foldl (\a c -> csubMap context eSubs c : a)
			eConds' (doCons ++ dsCons)
		nRules = 
			(if Volume.null doVolume || (Map.null doSubs && List.null doCons) then id
				else ((doVolume, doSubs, doCons, always) :)) $
			(if Map.null eSubs && List.null eConds then id
				else ((eVolume, eSubs, [], conjunction context eConds) :)) $
			(if Map.null ioSubs && List.null ioCons && isAlways oCond then id
				else ((oVolume, ioSubs, ioCons, oCond) :)) $ rules
		checkParts parts (pVolume, pSubs, pCons) = res where
			dpVolume = Volume.difference pVolume eVolume
			(ipSubs, dpSubs) = Map.partition (frefers $ memberOf oSubs) pSubs
			(ipCons, dpCons) = List.partition (frefers $ memberOf oSubs) pCons
			res =
				(if Volume.null dpVolume || (Map.null dpSubs && List.null dpCons) then id
					else ((dpVolume, dpSubs, dpCons) :)) $
				(if Map.null ipSubs && List.null ipCons then id
					else ((pVolume, ipSubs, ipCons) :)) $ parts
		nParts = List.foldl checkParts [] parts
		res = if Volume.null eVolume then accum else (nRules, nParts)
	(nRules, nParts) = List.foldl checkRules ([], [part]) rules
	res = List.foldl (\a (v, s, c) -> (v, s, c, always) : a) nRules nParts

-- Converts a rule set with conditions into a rule set without conditions, and a set of
-- amendments to the rule set.
applyConditions :: (Ord v, Formula k, Formula t)
	=> Int -> Volume 
	-> [(Volume, Map (Either v Int) (t (Either v Int)),
		[k (Either v Int)], Condition k t (Either v Int))]
	-> (Int, Volume, 
		[(Volume, Map (Either v Int) (t (Either v Int)), [k (Either v Int)])], 
		[(Volume, Map (Either v Int) (t (Either v Int)), [k (Either v Int)])])
applyConditions degree' volume' rules' = res where
	applyCondition
		accum@(degree', volume', proj, rules', ammends)
		rule@(rVolume, rSubs, rCons, rCond) = res where
			prVolume = proj rVolume
			applyProj proj = List.foldl (\a (v, s, c) -> case v of
				(Volume.null -> True) -> a
				nV -> (nV, s, c) : a) []
			applyNever = res where
				(nVolume, passProj) = Volume.cut volume' prVolume
				nRules = applyProj passProj rules'
				nAmmends = applyProj passProj ammends
				res = (degree', nVolume, passProj . proj, nRules, nAmmends)
			applyNormal cond = res where
				nDegree = degree' + degree rCond
				offsetVar (Left x) = x
				offsetVar (Right x) = Right (degree' + x)
				(nVolume, innerProj, passProj) = 
					Volume.refine volume' prVolume (volume rCond)
				nRules' = applyProj passProj rules'
				nRules = (prVolume, rSubs, rCons) : nRules'
				nAmmends' = applyProj passProj ammends
				nAmmends = List.foldl (\a (v, s, c) -> (innerProj v, 
					Map.map (fmap offsetVar) s, 
					List.map (fmap offsetVar) c) : a) nAmmends' (rules cond)
				res = (nDegree, nVolume, passProj . proj, nRules, nAmmends)
			res = if Volume.null prVolume then accum else case rCond of
				(isAlways -> True) -> (degree', volume', proj, 
					(prVolume, rSubs, rCons) : rules', ammends)
				(isNever -> True) -> applyNever
				cond -> applyNormal cond
	(nDegree, nVolume, _, nRules, nAmmends) =
		List.foldl applyCondition (degree', volume', id, [], []) rules'
	res = (nDegree, nVolume, nRules, nAmmends)

-- Removes sub-volumes from a condition in order to make it satisfy normalization rule 3.
prune :: Int -> Volume
	-> [(Volume, Map v (t (Either v Int)), [k (Either v Int)])]
	-> Condition k t v
prune degree volume rules = optimize $ Condition {
	degree = degree, volume = volume,
	rules = rules } -- TODO

-- Constructs a condition by merging a rule set (with conditions), and a set of rules
-- into a single condition.
construct :: (Ord v, Constraint r k t)
	=> r -> Int -> Volume
	-> [(Volume, Map (Either v Int) (t (Either v Int)),
		[k (Either v Int)], Condition k t (Either v Int))]
	-> [(Volume, Map (Either v Int) (t (Either v Int)), [k (Either v Int)])]
	-> Condition k t v
construct context degree volume rules ammends = res where
	nRules = List.foldl (insertRules context) rules ammends
	(nDegree, nVolume, fRules, nAmmends) = applyConditions degree volume nRules
	isLeft = either (const True) (const False)
	leftSubs = List.foldl (\a (v, s, c) -> case Map.filterWithKey (\k _ -> isLeft k) s of
		(Map.null -> True) -> if List.null c then a else (v, Map.empty, c) : a
		nS' -> (v, Map.mapKeysMonotonic (either id undefined) nS', c) : a) []
	augConds = List.map (\(v, s, c) -> (v, s, c, always))
	res = if List.null nAmmends
		then prune nDegree nVolume (leftSubs fRules)
		else construct context nDegree nVolume (augConds fRules) nAmmends

-- A condition that is always satisfied.
always :: Condition k t v
always = Condition { degree = 0, volume = Volume.single, rules = [] }
	
-- A condition that is never satisfied.
never :: Condition k t v
never = Condition { degree = 0, volume = Volume.empty, rules = [] }

-- Determines whether the given condition is always satisfied.
isAlways :: Condition k t v -> Bool
isAlways cond = not (Volume.null $ volume cond) && List.null (rules cond)

-- Determines whether the given condition is never satisfied.
isNever :: Condition k t v -> Bool
isNever cond = Volume.null $ volume cond

-- Constructs a condition that is satisfied exactly when the given constraint is
-- satisfied.
simple :: (Ord v, Formula k) => k v -> Condition k t v
simple con = simples [con]

-- Constructs a condition that is satisfied exactly when all of the given constraints are
-- satisfied.
simples :: (Ord v, Formula k) => [k v] -> Condition k t v
simples cons = Condition { degree = 0, volume = Volume.single,
	rules = [(Volume.single, Map.empty, List.map (fmap Left) cons)] }

-- Constructs a condition that is satisfied exactly when the given substitution is in
-- effect.
solution :: (Ord v, Formula t) => Map v (t v) -> Condition k t v
solution subs = Condition { degree = 0, volume = Volume.single,
	rules = [(Volume.single, Map.map (fmap Left) subs, [])] }

-- Constructs a condition that is satisfied exactly when the given substitution is in
-- effect.
solutionFromList :: (Ord v, Formula t) => [(v, t v)] -> Condition k t v
solutionFromList subs = solution $ Map.fromList subs

-- Applies a one-to-one mapping to the variables in a condition.
map :: (Ord v, Ord n, Formula k, Formula t) => (v -> n)
	-> Condition k t v -> Condition k t n
map m cond = res where
	mIn = either (Left . m) Right
	res = cond { rules = List.map (\(v, s, c) ->
		(v, Map.mapKeys m $ Map.map (fmap mIn) s, 
		List.map (fmap mIn) c)) $ rules cond }
		
-- Applies a substitution to a constraint.
sub :: (Ord v, Ord n, Constraint r k t) => r -> (v -> t n)
	-> Condition k t v -> Condition k t n
sub context m cond = res where
	mapVar (Left x) = fmap Left $ m x
	mapVar (Right x) = tvar context (Right x)
	nRules = List.map (\(v, s, c) -> (v, Map.empty, [],
		conjunction context (Map.foldlWithKey (\a v t ->
			ceq context (fmap Left $ m v) (tsub context mapVar t) : a)
			(List.map (csub context mapVar) c) s))) $ rules cond
	res = construct context (degree cond) (volume cond) nRules []
	
-- Existentially quantifies the given variables within the given condition.
exists :: (Ord v, Formula k, Formula t) => Set v -> Condition k t v -> Condition k t v
exists vars cond = existsFromList (Set.toList vars) cond

-- Existentially quantifies the given variables within the given condition.
existsFromList :: (Ord v, Formula k, Formula t) => [v]
	-> Condition k t v -> Condition k t v
existsFromList vars cond = res where
	(vMap, bound) = List.foldl
		(\(m, b) v -> (Map.insert v b m, b + 1))
		(Map.empty, 0) vars
	mapVar v = case Map.lookup v vMap of
		Just i -> Right i
		Nothing -> Left v
	res = existsRightInt bound (map mapVar cond)
	
-- Existentially quantifies all right variables (which must be enumerated) within the
-- given condition.
existsRight :: (Ord v, Ord n, Formula k, Formula t) => Set n
	-> Condition k t (Either v n) -> Condition k t v
existsRight vars cond = existsRightFromList (Set.toList vars) cond
	
-- Existentially quantifies all right variables (which must be enumerated) within the
-- given condition.
existsRightFromList :: (Ord v, Ord n, Formula k, Formula t) => [n]
	-> Condition k t (Either v n) -> Condition k t v
existsRightFromList vars cond = res where
	(vMap, bound) = List.foldl
		(\(m, b) v -> (Map.insert v b m, b + 1))
		(Map.empty, 0) vars	
	res = existsRightInt bound (map (either Left (Right . (Map.!) vMap)) cond)
	
-- Existentially quantifies all right variables (which must be less then the given 
-- bound) within the given condition.
existsRightInt :: (Ord v, Formula k, Formula t)
	=> Int -> Condition k t (Either v Int) -> Condition k t v
existsRightInt bound cond = res where
	mapVar (Left (Left x)) = Left x
	mapVar (Left (Right x)) = Right (degree cond + x)
	mapVar (Right x) = Right x
	lefts = Map.mapKeysMonotonic (either id undefined) .
		Map.filterWithKey (\k _ -> either (const True) (const False) k)
	(nRules, anyRemoved) = List.foldl (\(rules, anyRemoved) (v, s, c) ->
		case (lefts s, c) of
			(Map.null -> True, []) -> (rules, True)
			(subs, cons) -> ((v, Map.map (fmap mapVar) subs,
				List.map (fmap mapVar) cons) : rules, anyRemoved))
		([], False) $ rules cond
	res = if anyRemoved then prune (degree cond + bound) (volume cond) nRules
		else Condition { degree = degree cond + bound,
			volume = volume cond, rules = nRules }

-- Computes the conjunction of many conditions.
conjunction :: (Ord v, Constraint r k t) => r -> [Condition k t v] -> Condition k t v
conjunction _ [] = always
conjunction context (head : []) = head
conjunction context (head : tail) = construct context (degree head) (volume head)
	((List.foldl (\a cond -> (volume head, Map.empty, [], map Left cond) : a) $
	List.map (\(v, s, c) -> (v, Map.mapKeysMonotonic Left s, c, always)) $
	rules head) tail) []

-- Computes the disjunction of many conditions.
disjunction :: (Ord v) => [Condition k t v] -> Condition k t v
disjunction [] = never
disjunction (cond : _) | isAlways cond = always
disjunction (cond : rem) | isNever cond = disjunction rem
disjunction (cond : rem) = res where
	pushCondition Nothing _ = Nothing
	pushCondition (Just state) cond | isNever cond = Just state
	pushCondition (Just _) cond | isAlways cond = Nothing
	pushCondition (Just (degree', volume', rules')) cond = res where
		nDegree = max degree' (degree cond)
		(nVolume, lProj, rProj) = Volume.sum volume' (volume cond)
		insertRules m accum (v, s, c) = (m v, s, c) : accum
		nRules' = List.foldl (insertRules lProj) [] rules'
		nRules = List.foldl (insertRules rProj) nRules' $ rules cond
		res = Just (nDegree, nVolume, nRules)
	state = Just (degree cond, volume cond, rules cond)
	res = case List.foldl pushCondition state rem of
		Just (nDegree, nVolume, nRules) -> Condition {
			degree = nDegree, volume = nVolume, rules = nRules }
		Nothing -> always

-- Constructs a condition that is satisfied exactly when both of the given conditions
-- are satisfied.
infixl 3 &&^
(&&^) :: (Ord v, Constraint () k t)
	=> Condition k t v -> Condition k t v -> Condition k t v
(&&^) x y = conjunction () [x, y]
	
-- Constructs a condition that is satisfied exactly when either of the given conditions
-- are satisfied.
infixl 2 ||^
(||^) :: (Ord v)
	=> Condition k t v -> Condition k t v -> Condition k t v
(||^) x y = disjunction [x, y]

-- Constructs a condition that is satisfied exactly when the given terms are equivalent.
infix 4 ==^
(==^) :: (Ord v, Constraint () k t) => t v -> t v -> Condition k t v
(==^) x y = ceq () x y
		
-- Refines the constraints in a condition.
bind :: (Ord v, Constraint r k t) => r -> (forall n. (Ord n) => k n -> Condition k t n)
	-> Condition k t v -> Condition k t v
bind context m cond = construct context (degree cond) (volume cond)
	(List.map (\(v, s, c) -> (v, Map.mapKeysMonotonic Left s, [],
		conjunction context $ List.map m c)) (rules cond)) []


-- Gets the volume of a condition is affected by constraints.
constraintVolume :: Condition k t v -> Volume
constraintVolume cond = List.foldl (\a (v, _, c) -> if List.null c then a
	else Volume.union a v) Volume.empty $ rules cond
		
-- Filters a condition to only include the given sub-volume.
filterVolume :: Condition k t v -> Volume -> Condition k t v
filterVolume cond volume' = cond { volume = volume', rules = List.foldl (\a (v, s, c) ->
	case Volume.difference v volume' of
		(Volume.null -> True) -> a
		nV -> (nV, s, c) : a) [] $ rules cond }


-- Reinterprets the given condition as a disjunction of a maximal set of solutions and
-- a non-solution condition. Note that returned solutions can reference existentially-
-- quantified variables.
extract :: (Ord v) => Condition k t v -> ([Map v (t (Either v Int))], Condition k t v)
extract cond | isAlways cond = ([Map.empty], never)
extract cond | isNever cond = ([], never)
extract cond = res where
	cVolume = constraintVolume cond
	sVolume = Volume.difference (volume cond) cVolume
	refine accum (oVolume, oSubs, _) = res where
		refineOne accum (sVolume, sSubs) = nAccum where
			intersection = Volume.intersection sVolume oVolume
			difference = Volume.difference sVolume intersection
			nAccum = if Volume.null intersection then (sVolume, sSubs) : accum
				else (intersection, Map.unionWith undefined oSubs sSubs) :
					(if Volume.null difference then accum 
					else (difference, sSubs) : accum)
		res = List.foldl refineOne [] accum
	solutions = List.map snd $ List.foldl refine [(sVolume, Map.empty)] $ rules cond
	nCond = filterVolume cond cVolume
	res = (solutions, nCond)
	
-- Reinterprets the given condition as a disjunction of a maximal set of solutions and
-- a non-solution condition.
extractToList :: (Ord v) => Condition k t v
	-> ([[(v, t (Either v Int))]], Condition k t v)
extractToList cond = res where
	(subs, nCond) = extract cond
	nSubs = List.map Map.toList subs
	res = (nSubs, nCond)

-- Determines whether the given condition has a solution.
isSolvable :: (Ord v) => Condition k t v -> Bool
isSolvable cond = not (Volume.contains (constraintVolume cond) (volume cond))