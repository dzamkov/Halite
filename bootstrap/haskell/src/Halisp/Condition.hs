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
import Prelude.Extras (Ord1, Lift1 (..))
import Halisp.Volume (Volume)
import qualified Halisp.Volume as Volume
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List
import Data.Maybe (fromJust)

-- Identifies a type constructor for a formula, which includes both terms and constraints.
class (Ord1 f) => Formula f where

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
	-- in some sub-volume of this volume if all substitutions and constraints that
	-- intersect that sub-volume are satisfied.
	volume :: Volume,
	
	-- The set of substitutions that apply to a condition.
	subs :: Map (v, Lift1 t (Either v Int)) Volume,
	
	-- The set of constraints that apply to a condition.
	cons :: Map (Lift1 k (Either v Int)) Volume }
	
-- Makes a condition with exactly the given data.
make :: (Ord v, Ord1 t, Ord1 k) => Int -> Volume
	-> [(v, t (Either v Int), Volume)]
	-> [(k (Either v Int), Volume)]
	-> Condition k t v
make degree volume subs cons = Condition {
	degree = degree, volume = volume,
	subs = Map.fromList $ List.map (\(v, t, u) -> ((v, Lift1 t), u)) $ subs,
	cons = Map.fromList $ List.map (\(c, v) -> (Lift1 c, v)) $ cons }
	
-- Makes a simple (one-case) condition with exactly the given data.
makeSimple :: (Ord v, Ord1 t, Ord1 k) => Int
	-> [(v, t (Either v Int))] 
	-> [(k (Either v Int))]
	-> Condition k t v
makeSimple degree subs cons = Condition {
	degree = degree, volume = Volume.single,
	subs = Map.fromList $ List.map (\(v, t) -> ((v, Lift1 t), Volume.single)) $ subs,
	cons = Map.fromList $ List.map (\c -> (Lift1 c, Volume.single)) $ cons }

instance (Show v, Show (k (Either v Int)), Show (t (Either v Int))) 
	=> Show (Condition k t v) where
	showsPrec _ cond | isAlways cond = ("always" ++ )
	showsPrec _ cond | isNever cond = ("never" ++)
	showsPrec 11 cond = ("(" ++) . showsPrec 0 cond . (")" ++)
	showsPrec _ cond | isSimple cond = res where
		isSimple cond = 
			Map.foldl (\a v -> a && v == volume cond) True (subs cond) &&
			Map.foldl (\a v -> a && v == volume cond) True (cons cond)
		res = ("makeSimple " ++) . showsPrec 11 (degree cond) . (" " ++) .
			showsPrec 11 (List.map (\((v, lower1 -> t), u) -> 
				(v, t)) $ Map.toList $ subs cond) . (" " ++) .
			showsPrec 11 (List.map (\(lower1 -> c, v) -> c) $ Map.toList $ cons cond)
	showsPrec _ cond = ("make " ++) . showsPrec 11 (degree cond) . (" " ++) .
		showsPrec 11 (volume cond) . (" " ++) .
		showsPrec 11 (List.map (\((v, lower1 -> t), u) -> 
			(v, t, u)) $ Map.toList $ subs cond) . (" " ++) .
		showsPrec 11 (List.map (\(lower1 -> c, v) -> (c, v)) $ Map.toList $ cons cond)

-- TODO: Prevent overflow of existential variables. 'degree' should not grow without
-- bound.

-- VOCAB: a rule is a constraint or substitution.

-- Rules for condition normalization:
-- 1. If a substitution intersects another rule, that rule must not refer to the variable
--    assigned in the substitution.
-- 2. The volume for a rule may not be empty.
-- 3. For any volume in a condition, there must not exist another volume whose contained
--    rules are a proper subset of the first volume's.

-- Optimizes the internal volumes of a condition.
optimize :: Condition k t v -> Condition k t v
optimize cond = res where
	volumes = (Map.elems $ subs cond) ++ (Map.elems $ cons cond)
	(nVolume, proj) = Volume.optimize (volume cond) volumes
	res = Condition {
		degree = degree cond,
		volume = nVolume,
		subs = Map.map proj $ subs cond,
		cons = Map.map proj $ cons cond }
		
-- Inserts a substitution into a substitution map, preserving normalization rule 1. If the
-- substitution conflicts with an existing substitution, an equivalence condition is
-- created and inserted into a given list.
insertSub :: (Ord v, Constraint r k t) => r
	-> (Map (v, Lift1 t v) Volume, [(Condition k t v, Volume)])
	-> (v, t v, Volume)
	-> (Map (v, Lift1 t v) Volume, [(Condition k t v, Volume)])
insertSub context (subs, conds) (var, term, volume) = res where
	checkSub accum@(volume, aSubs, conds) (oVar, lower1 -> oTerm) oVolume = res where
		intersection = Volume.intersection volume oVolume
		resI = case (var == oVar, frefers (== oVar) term, frefers (== var) oTerm) of
			(True, _, _) -> ((Volume.difference volume oVolume, aSubs, 
				(ceq context term oTerm, intersection) : conds), oVolume)
			(False, True, True) -> ((Volume.difference volume oVolume, aSubs,
				(ceq context (tvar context var) (tsubOne context oVar oTerm term),
				intersection) : conds), oVolume)
			(False, False, True) -> ((volume, (oVar, tsubOne context var term oTerm,
				intersection) : aSubs, conds), Volume.difference oVolume volume)
			(False, True, False) -> ((Volume.difference volume oVolume, (var, tsubOne
				context oVar oTerm term, intersection) : aSubs, conds), oVolume)
			(False, False, False) -> ((volume, aSubs, conds), oVolume)
		res = if Volume.null intersection then (accum, oVolume) else resI
	((nVolume, aSubs, nConds), nSubs'') =
		Map.mapAccumWithKey checkSub (volume, [], conds) subs
	nSubs' = Map.insertWith Volume.union (var, Lift1 term) nVolume nSubs''
	nSubs = List.foldl (\subs (var, term, vol) ->
		Map.insertWith Volume.union (var, Lift1 term) vol subs) nSubs' aSubs
	res = (nSubs, nConds)

-- Inserts a constraint into a constraint map, preserving normalizaation rules 1 and 2.
insertCon :: (Ord v, Constraint r k t) => r
	-> Map (v, Lift1 t v) Volume
	-> ([(k v, Volume)], [(Condition k t v, Volume)])
	-> (k v, Volume)
	-> ([(k v, Volume)], [(Condition k t v, Volume)])
insertCon context subs (cons, conds) (con, volume) = res where
	checkCon accum@(volume, conds) (oVar, lower1 -> oTerm) oVolume = res where
		intersection = Volume.intersection volume oVolume
		resI = if frefers (== oVar) con
			then (Volume.difference volume oVolume,
				(csubOne context oVar oTerm con, intersection) : conds)
			else accum
		res = if Volume.null intersection then accum else resI
	(nVolume, nConds) = Map.foldlWithKey checkCon (volume, conds) subs
	nCons = if Volume.null nVolume then cons else (con, nVolume) : cons
	res = (nCons, nConds)

-- Breaks a condition (occupying a volume) down into substitutions and constraints.
deconstruct :: (Ord v, Formula k, Formula t)
	=> (Int, Volume, Volume -> Volume, 
		[((Either v Int), t (Either v Int), Volume)], [(k (Either v Int), Volume)])
	-> (Condition k t (Either v Int), Volume)
	-> (Int, Volume, Volume -> Volume, 
		[((Either v Int), t (Either v Int), Volume)], [(k (Either v Int), Volume)])
deconstruct state (cond, _) | isAlways cond = state
deconstruct (degree, full, proj, subs, cons) (cond, volume') | isNever cond = res where
	pVolume = proj volume'
	(nFull, passProj) = Volume.cut full pVolume
	nProj = passProj . proj
	nSubs = List.map (\(a, b, v) -> (a, b, passProj v)) subs
	nCons = List.map (\(a, v) -> (a, passProj v)) cons
	res = (degree, nFull, nProj, nSubs, nCons)
deconstruct (degree', full, proj, subs', cons') (cond, volume') = res where
	nDegree = degree' + degree cond
	offsetVar (Left x) = x
	offsetVar (Right x) = Right (degree' + x)
	pVolume = proj volume'
	(nFull, innerProj, passProj) = Volume.refine full pVolume (volume cond)
	nProj = passProj . proj
	nSubs' = List.map (\(a, b, v) -> (a, b, passProj v)) subs'
	nCons' = List.map (\(a, v) -> (a, passProj v)) cons'
	nSubs = Map.foldlWithKey (\a (v, lower1 -> t) u -> 
		(v, fmap offsetVar t, innerProj u) : a) nSubs' (subs cond)
	nCons = Map.foldlWithKey (\a (lower1 -> c) v -> 
		(fmap offsetVar c, innerProj v) : a) nCons' (cons cond)
	res = (nDegree, nFull, nProj, nSubs, nCons)

-- Removes sub-volumes from a condition in order to make it satisfy normalization rule 3.
prune :: Int -> Volume -> Map (v, Lift1 t (Either v Int)) Volume
	-> Map (Lift1 k (Either v Int)) Volume -> Condition k t v
prune degree volume subs cons = optimize $ Condition {
	degree = degree, volume = volume,
	subs = subs, cons = cons } -- TODO

-- Constructs a condition by merging a substitution map (obeying normalization rule 1),
-- a set of substitutions, a set of constraints, and a set of conditions.
construct :: (Ord v, Constraint r k t) => r -> Int -> Volume
	-> Map (Either v Int, Lift1 t (Either v Int)) Volume
	-> [(Either v Int, t (Either v Int), Volume)]
	-> [(k (Either v Int), Volume)]
	-> [(Condition k t (Either v Int), Volume)]
	-> Condition k t v
construct context degree volume subs aSubs aCons aConds = res where
	(nDegree, nVolume, proj, naSubs, naCons) =
		List.foldl deconstruct (degree, volume, id, aSubs, aCons) aConds
	nSubs'' = Map.map proj subs
	(nSubs', naConds1) = List.foldl (insertSub context) (nSubs'', []) naSubs
	nSubs = Map.filter (not . Volume.null) nSubs'
	(nCons, naConds2) = List.foldl (insertCon context nSubs) ([], []) naCons
	lefts = Map.mapKeysMonotonic (\(v, t) -> (either id undefined v, t)) .
		Map.filterWithKey (\(v, _) _ -> either (const True) (const False) v)
	fromListLift1 = Map.fromList . List.map (\(c, v) -> (Lift1 c, v))
	res = if List.null naConds1
		then (if List.null naConds2
			then prune nDegree nVolume (lefts nSubs) (fromListLift1 nCons)
			else construct context nDegree nVolume nSubs [] nCons naConds2)
		else construct context nDegree nVolume nSubs [] naCons naConds1

-- A condition that is always satisfied.
always :: Condition k t v
always = Condition {
	degree = 0, volume = Volume.single,
	subs = Map.empty, cons = Map.empty }
	
-- A condition that is never satisfied.
never :: Condition k t v
never = Condition {
	degree = 0, volume = Volume.empty,
	subs = Map.empty, cons = Map.empty }

-- Determines whether the given condition is always satisfied.
isAlways :: Condition k t v -> Bool
isAlways cond = not (Volume.null $ volume cond)
	&& Map.null (subs cond) && Map.null (cons cond)

-- Determines whether the given condition is never satisfied.
isNever :: Condition k t v -> Bool
isNever cond = Volume.null $ volume cond

-- Constructs a condition that is satisfied exactly when the given constraint is
-- satisfied.
simple :: (Ord v, Formula k) => k v -> Condition k t v
simple con = Condition {
	degree = 0, volume = Volume.single,
	subs = Map.empty, cons = Map.singleton (Lift1 $ fmap Left con) Volume.single }

-- Constructs a condition that is satisfied exactly when all of the given constraints are
-- satisfied.
simples :: (Ord v, Formula k) => [k v] -> Condition k t v
simples cons = Condition {
	degree = 0, volume = Volume.single,
	subs = Map.empty, cons = Map.fromList $ List.map (\c ->
		(Lift1 $ fmap Left c, Volume.single)) cons }

-- Constructs a condition that is satisfied exactly when the given substitution is in
-- effect.
solution :: (Ord v, Formula t) => [(v, t v)] -> Condition k t v
solution subs = Condition {
	degree = 0, volume = Volume.single,
	subs = Map.fromList $ List.map (\(v, t) ->
		((v, Lift1 $ fmap Left t), Volume.single)) subs,
	cons = Map.empty }

-- Applies a one-to-one mapping to the variables in a condition.
map :: (Ord v, Ord n, Formula k, Formula t) => (v -> n)
	-> Condition k t v -> Condition k t n
map m cond = res where
	mIn = either (Left . m) Right
	res = cond {
		subs = Map.mapKeys (\(v, lower1 -> t) -> (m v, Lift1 $ fmap mIn t)) $ subs cond,
		cons = Map.mapKeys (Lift1 . fmap mIn . lower1) $ cons cond }
		
-- Applies a substitution to a constraint.
sub :: (Ord v, Ord n, Constraint r k t) => r -> (v -> t n)
	-> Condition k t v -> Condition k t n
sub context m cond = res where
	mapVar (Left x) = fmap Left $ m x
	mapVar (Right x) = tvar context (Right x)
	conds' = Map.foldlWithKey (\a (v, lower1 -> t) u ->
		(ceq context (fmap Left $ m v) (tsub context mapVar t), u) : a) [] (subs cond)
	conds = Map.foldlWithKey (\a (lower1 -> c) v ->
		(csub context mapVar c, v) : a) conds' (cons cond)
	res = construct context (degree cond) (volume cond) Map.empty [] [] conds
	
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
	nSubs = Map.mapKeys (\(v, lower1 -> t) -> 
		(either id undefined v, Lift1 $ fmap mapVar t)) $
		Map.filterWithKey (\(v, _) _ -> either (const True) (const False) v) (subs cond)
	nCons = Map.mapKeys (Lift1 . fmap mapVar . lower1) (cons cond)
	res = if Map.size nSubs < Map.size (subs cond)
		then prune (degree cond + bound) (volume cond) nSubs nCons
		else Condition { degree = degree cond + bound, volume = volume cond,
			subs = nSubs, cons = nCons }

-- Computes the conjunction of many conditions.
conjunction :: (Ord v, Constraint r k t) => r -> [Condition k t v] -> Condition k t v
conjunction _ [] = always
conjunction context conds = construct context 0 Volume.single Map.empty [] [] $
	List.map (\c -> (map Left c, Volume.single)) conds

-- Computes the disjunction of many conditions.
disjunction :: (Ord v, Ord1 t, Ord1 k) => [Condition k t v] -> Condition k t v
disjunction [] = never
disjunction (cond : _) | isAlways cond = always
disjunction (cond : rem) | isNever cond = disjunction rem
disjunction (cond : rem) = res where
	pushCondition Nothing _ = Nothing
	pushCondition (Just state) cond | isNever cond = Just state
	pushCondition (Just _) cond | isAlways cond = Nothing
	pushCondition (Just (degree', volume', subs', cons')) cond = res where
		nDegree = max degree' (degree cond)
		(nVolume, lProj, rProj) = Volume.sum volume' (volume cond)
		nSubs = Map.unionWith undefined (Map.map lProj subs') (Map.map rProj $ subs cond)
		nCons = Map.unionWith undefined (Map.map lProj cons') (Map.map rProj $ cons cond)
		res = Just (nDegree, nVolume, nSubs, nCons)
	state = Just (degree cond, volume cond, subs cond, cons cond)
	res = case List.foldl pushCondition state rem of
		Just (nDegree, nVolume, nSubs, nCons) -> Condition {
			degree = nDegree, volume = nVolume,
			subs = nSubs, cons = nCons }
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
(||^) :: (Ord v, Ord1 t, Ord1 k)
	=> Condition k t v -> Condition k t v -> Condition k t v
(||^) x y = disjunction [x, y]

-- Constructs a condition that is satisfied exactly when the given terms are equivalent.
infix 4 ==^
(==^) :: (Ord v, Constraint () k t) => t v -> t v -> Condition k t v
(==^) x y = ceq () x y
		
-- Refines the constraints in a condition.
bind :: (Ord v, Constraint r k t) => r -> (forall n. (Ord n) => k n -> Condition k t n)
	-> Condition k t v -> Condition k t v
bind context m cond = res where
	res = construct context (degree cond) (volume cond)
		(Map.mapKeysMonotonic (\(v, t) -> (Left v, t)) $ subs cond)
		[] [] $ Map.foldlWithKey (\a (lower1 -> c) v -> (m c, v) : a) [] $ cons cond
		
-- Filters a condition to only include the given sub-volume.
filterVolume :: (Ord v) => Condition k t v -> Volume -> Condition k t v
filterVolume cond volume' = res where
	differenceOrNothing volume = res where
		nVolume = Volume.difference volume volume'
		res = if Volume.null nVolume then Nothing else Just nVolume
	res = cond { volume = volume',
		subs = Map.mapMaybe differenceOrNothing $ subs cond,
		cons = Map.mapMaybe differenceOrNothing $ cons cond }

-- Reinterprets the given condition as a disjunction of a maximal set of solutions and
-- a non-solution condition. Note that returned solutions can reference existentially-
-- quantified variables.
extract :: (Ord v) => Condition k t v -> ([Map v (t (Either v Int))], Condition k t v)
extract cond | isAlways cond = ([Map.empty], never)
extract cond | isNever cond = ([], never)
extract cond = res where
	cVolume = Map.foldl Volume.union Volume.empty $ cons cond
	sVolume = Volume.difference (volume cond) cVolume
	refine accum (var, lower1 -> term) volume = res where
		refineOne accum (subs, vol) = nAccum where
			intersection = Volume.intersection vol volume
			difference = Volume.difference vol volume
			nAccum = if Volume.null intersection then (subs, volume) : accum
				else (Map.insert var term subs, intersection) : (if Volume.null difference
					then accum else (subs, difference) : accum)
		res = List.foldl refineOne [] accum
	solutions = List.map fst $ Map.foldlWithKey refine [(Map.empty, sVolume)] $ subs cond
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
isSolvable cond = not $ List.null $ fst $ extract cond