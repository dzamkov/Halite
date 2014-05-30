{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
	isSolvable,
	coalesce
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
	
class (Formula k, Term r t) => Constraint r k t where
	
	-- Applies a substitution to the variables in a constraint.
	csub :: (Ord v, Ord n) => r -> (v -> t n) -> k v -> Condition k t n
	
	-- Gets a condition that is satisfied when the two given terms are equal
	-- (indistinguishable inside constraints).
	ceq :: (Ord v) => r -> t v -> t v -> Condition k t v
	

-- Gives determined values to a set of variables, with values represented by terms which
-- may reference other variables.
type Substitution t v n = Map v (t n)

-- Describes restrictions on a conditional case using a substitution on a set of
-- variables, and a set of constraints. The type 'v' is for variables which may be
-- determined (substituted) in the rule, while the type 'n' is for variables which may be
-- referenced in the rule.
type Rule k t v n = (Substitution t v n, [k n])
	
-- A boolean formula (including conjunctions and disjunctions, but lacking negation)
-- relating constraints.
data Condition k t v = Condition {

	-- The index of the next unused free variable in a condition. Free variables appear
	-- as "Right" variables in constraints and substitutions.
	degree :: Int,

	-- A volume representing the cases covered by a condition. See 'rules' for more
	-- information.
	volume :: Volume,
	
	-- TODO: Try changing the storage structure of rules to store substitutions and
	-- constraints as seperate maps, indexed by value rather than by volume. This will
	-- allow automatic coalescing.
	
	-- The set of rules that apply to a condition. Each rule is associated with the volume
	-- of cases it applies to. Rules consist of substitutions of bound variables, and
	-- constraints between both free and bound variables. In order for the condition to be
	-- satisfied, there must be some non-empty sub-volume within its volume where all
	-- intersecting rules are satisfied.
	rules :: Map Volume (Rule k t v (Either v Int)) }

deriving instance (Show v, Show (k (Either v Int)), Show (t (Either v Int)))
	=> Show (Condition k t v)

-- TODO: Prevent overflow of existential variables. 'degree' should not grow without
-- bound.	

-- Vocab: A rule, X, is said to be "dependent" on another rule, Y, if X and Y have an
-- intersecting volume and X contains a constraint or substitution which references
-- or substitutes a variable determined in Y. X is said to be "independent" of Y if X is 
-- not dependent on Y. Two rules, X and Y, are said to be "independent" if neither X is 
-- dependent on Y or Y is dependent on X.
	
-- Rules for condition normalization:
-- 1. All rules within a condition must be pairwise independent.
-- 2. The volume for a rule may not be empty.
-- 3. A rule may not be empty (no substitution or constraints).
-- 4. For any volume in a condition, there must not exist another volume whose contained
--    rules are a proper subset of the first volume's.

-- Optimizes the internal volumes of a condition.
optimize :: Condition k t v -> Condition k t v
optimize cond = res where
	(nVolume, proj) = Volume.optimize (volume cond) (Map.keys $ rules cond)
	nRules = Map.mapKeys proj $ rules cond
	res = Condition { degree = degree cond, volume = nVolume, rules = nRules }

-- Determines whether the given rule is empty (always satisfied).
nullRule :: Rule k t v n -> Bool
nullRule (subs, []) = Map.null subs
nullRule _ = False

-- Merges two rules.
mergeRules :: (Ord v) => Rule k t v n -> Rule k t v n -> Rule k t v n
mergeRules (xSubs, xCons) (ySubs, yCons) = 
	(Map.unionWith undefined xSubs ySubs, xCons ++ yCons)

-- Applies a substitution to a rule, assuming that the substitution does not reference
-- any variables determined by the rule. The result is returned in three parts, a rule
-- that is independent of the substitution, a rule that is dependent on the substitution,
-- and a condition which represents the dependent part after the substitution is applied.
subRule :: (Ord v, Ord n, Constraint r k t) => r -> Substitution t n n -> Rule k t v n
	-> (Rule k t v n, Rule k t v n, (Substitution t v n, Condition k t n))
subRule context s (subs, cons) = res where
	inS v = Map.member v s
	app var = maybe (tvar context var) id $ Map.lookup var s
	(dSubs, iSubs) = Map.partition (frefers inS) subs
	(dCons, iCons) = List.partition (frefers inS) cons
	dnSubs = Map.map (tsub context $ app) dSubs
	dnCond = conjunction context $ List.map (csub context app) dCons
	res = ((iSubs, iCons), (dSubs, dCons), (dnSubs, dnCond))
	
-- Applies a substitution into a rule, like 'subRule', but can be used when the
-- substitution and rule are interdependent.
subRuleD :: (Ord v, Constraint r k t) => r -> Substitution t v v -> Rule k t v v
	-> (Rule k t v v, Rule k t v v, (Substitution t v v, Condition k t v))
subRuleD context s (subs, cons) = res where
	eSubs = Map.intersectionWith (,) s subs
	nS = Map.difference s eSubs
	innS v = Map.member v nS
	(dSubs', iSubs) = Map.partition (frefers innS) (Map.difference subs eSubs)
	(dCons, iCons) = List.partition (frefers innS) cons
	dSubs = Map.union dSubs' (Map.map snd eSubs)
	insertSub var val (subs, conds) = res where
		nVal = tsub context (\v -> maybe (tvar context v) id $ Map.lookup v subs) val
		nSubs' = Map.map (tsub context
			(\v -> if v == var then nVal else tvar context v)) subs
		nSubs = Map.insert var nVal nSubs'
		res = if frefers (var ==) nVal
			then (subs, ceq context (tvar context var) nVal : conds)
			else (nSubs, conds)
	(dnSubs, dnConds'') = Map.foldrWithKey insertSub (dSubs, []) nS
	app var = maybe (tvar context var) id $ Map.lookup var dnSubs
	dnConds' = List.foldl (\a cons -> csub context app cons : a) dnConds'' dCons
	dnConds = List.foldl (\a (x, y) -> ceq context x y : a) dnConds' (Map.elems eSubs)
	dnCond = conjunction context dnConds
	res = ((iSubs, iCons), (dSubs, dCons), (dnSubs, dnCond))

-- Constructs a condition from a degree, volume and a set of pairwise independent rules.
-- This function performs pruning on the rules to satisfy normalization rule 4.
prune :: (Ord v) => Int -> Volume 
	-> Map Volume (Rule k t v (Either v Int))
	-> Condition k t v
prune degree volume rules = res where
	pruneRules oVolume rules | Map.null rules = (Volume.empty, Volume.empty)
	pruneRules oVolume rules | (Map.size rules == 1) = res where
		(iVolume, _) = Map.findMax rules
		pVolume' = Volume.intersection iVolume oVolume
		pVolume = if Volume.contains iVolume pVolume' then Volume.empty else pVolume'
		res = (pVolume, iVolume)
	pruneRules oVolume rules = res where
		parts = Map.splitRoot rules
		pruneParts loVolume [] = (Volume.empty, Volume.empty)
		pruneParts loVolume (part : rem) = res where
			toVolume = Volume.union loVolume roVolume
			(ipVolume, iVolume) = pruneRules toVolume part
			liVolume = Volume.union loVolume iVolume
			(rpVolume, roVolume) = pruneParts liVolume rem
			res = (Volume.union rpVolume ipVolume, Volume.union roVolume iVolume)
		res = pruneParts oVolume parts
	(pVolume, iVolume) = pruneRules Volume.empty rules
	(nVolume, proj) = Volume.cut volume pVolume
	nRules = Map.delete Volume.empty $ Map.mapKeysWith mergeRules proj rules
	cond = Condition { degree = degree, volume = nVolume, rules = nRules }
	res = if Volume.contains volume iVolume then cond else always

-- Merges a set of conditions, each occupying a volume, into a single consistent list of
-- rules. A projection from the original space to the returned space is also returned.
mergeConditions :: (Ord v, Formula k, Formula t) => Int -> Volume
	-> [[(Volume, Rule k t (Either v Int) (Either v Int))]]
	-> [(Volume, Condition k t (Either v Int))]
	-> (Int, Volume, Volume -> Volume,
		[[(Volume, Rule k t (Either v Int) (Either v Int))]])
mergeConditions degree' volume' rem conds = res where
	pushCondition state (_, cond) | isAlways cond = state
	pushCondition (degree, volume', proj, rem) (cVolume', cond) | isNever cond = res where
		cVolume = proj cVolume'
		(nVolume, passProj) = Volume.cut volume' cVolume
		nProj = passProj . proj
		updateRule accum (volume, rule) = res where
			nVolume = passProj volume
			res = if Volume.null nVolume then accum else (nVolume, rule) : accum
		nRem = List.map (List.foldl updateRule []) rem
		res = (degree, nVolume, nProj, nRem)
	pushCondition (degree', volume', proj, rem) (cVolume', cond) = res where
		nDegree = degree' + degree cond
		offsetVar (Left x) = x
		offsetVar (Right x) = Right (degree' + x)
		offsetRule (subs, cons) = 
			(Map.map (fmap offsetVar) subs,
			List.map (fmap offsetVar) cons)
		cVolume = proj cVolume'
		(nVolume, innerProj, passProj) = Volume.refine volume' cVolume (volume cond)
		nProj = passProj . proj
		nRem' = List.map (List.map (\(vol, r) -> (passProj vol, r))) rem
		cRules = List.map (\(vol, r) -> (innerProj vol, offsetRule r)) $ 
			Map.assocs $ rules cond
		nRem = cRules : nRem'
		res = (nDegree, nVolume, nProj, nRem)
	res = List.foldl pushCondition (degree', volume', id, rem) conds
	
-- Constructs a condition from a degree, volume, base set of rules, and a set of
-- "ammendments" to those rules. All Ammendments must be independent of the base rule set.
-- Ammendments are grouped such that all ammendments within a group are pairwise
-- independent.
construct :: forall r k t v. (Ord v, Constraint r k t) => r -> Int -> Volume
	-> Map Volume (Rule k t v (Either v Int))
	-> [[(Volume, Rule k t (Either v Int) (Either v Int))]]
	-> Condition k t v
construct _ degree volume rules [] = optimize $ prune degree volume rules
construct context degree volume rules (group : rem) = res where
	insertAmmend state (aVolume, aRule) = res where
		(degree, volume, proj, rules, groupRules, rem) = state
		(aSubs, aCons) = aRule
		apVolume = proj aVolume
		aLeftSubs = Map.mapKeysMonotonic fromJust $ Map.delete Nothing $ 
			Map.mapKeys (either Just (const Nothing)) aSubs
		updateRule bVolume bRule (conds, rules) = res where
			(biRule, bdRule, (bdnSubs, bdnCond)) = subRule context aSubs bRule
			iVolume = Volume.intersection bVolume aVolume
			dVolume = Volume.difference bVolume aVolume
			nRules'' = if nullRule biRule then rules 
				else Map.insertWith mergeRules bVolume biRule rules
			nRules' = if nullRule bdRule || Volume.null dVolume then nRules''
				else Map.insertWith mergeRules dVolume bdRule nRules''
			nRules = if Map.null bdnSubs then nRules'
				else Map.insertWith mergeRules iVolume (bdnSubs, []) nRules'
			nConds = if isAlways bdnCond then conds
				else (proj iVolume, bdnCond) : conds
			res = if Volume.null iVolume then (conds, Map.insert bVolume bRule rules)
				else (nConds, nRules)
		(conds', nRules) = Map.foldrWithKey updateRule ([], Map.empty) rules
		updateRemGroup (rem, conds) group = res where
			updateRemRule :: -- There's a weird error if this type signature is removed
				([(Volume, Rule k t (Either v Int) (Either v Int))],
				[(Volume, Condition k t (Either v Int))])
				-> (Volume, Rule k t (Either v Int) (Either v Int))
				-> ([(Volume, Rule k t (Either v Int) (Either v Int))],
				[(Volume, Condition k t (Either v Int))])
			updateRemRule (group, conds) (rVolume, rRule) = res where
				(riRule, rdRule, (rdnSubs', rdnCond)) = subRuleD context aSubs rRule
				rdnSubs = Map.difference rdnSubs' aSubs
				iVolume = Volume.intersection rVolume apVolume
				dVolume = Volume.difference rVolume apVolume
				nGroup'' = if nullRule riRule then group
					else (rVolume, riRule) : group
				nGroup' = if nullRule rdRule || Volume.null dVolume then nGroup''
					else (dVolume, rdRule) : nGroup''
				nGroup = if Map.null rdnSubs then nGroup'
					else (iVolume, (rdnSubs, [])) : nGroup'
				nConds = if isAlways rdnCond then conds
					else (iVolume, rdnCond) : conds
				res = if Volume.null iVolume then ((rVolume, rRule) : group, conds)
					else (nGroup, nConds)
			(nGroup, nConds) = List.foldl updateRemRule ([], conds) group
			res = if List.null nGroup then (rem, nConds) else (nGroup : rem, nConds)
		(nRem', conds) = foldl updateRemGroup ([], conds') rem
		(nDegree, nVolume, dProj, nRem) = mergeConditions degree volume nRem' conds
		nGroupRules' = if Map.null aLeftSubs && List.null aCons then groupRules
			else (apVolume, (aLeftSubs, aCons)) : groupRules
		nGroupRules = List.map (\(v, r) -> (dProj v, r)) nGroupRules'
		nProj = dProj . proj
		res = (nDegree, nVolume, nProj, nRules, nGroupRules, nRem)
	(nDegree, nVolume, proj, nRules'', groupRules', nRem) =
		List.foldl insertAmmend (degree, volume, id, rules, [], rem) group
	nRules' = Map.delete Volume.empty $ Map.mapKeys proj nRules''
	groupRules = Map.delete Volume.empty $ Map.fromListWith mergeRules groupRules'
	nRules = Map.unionWith mergeRules nRules' groupRules
	res = construct context nDegree nVolume nRules nRem

-- Like 'construct', but allows condition ammendments in addition to rule ammendments.
constructFull :: (Ord v, Constraint r k t) => r -> Int -> Volume
	-> Map Volume (Rule k t v (Either v Int))
	-> [[(Volume, Rule k t (Either v Int) (Either v Int))]]
	-> [(Volume, Condition k t (Either v Int))]
	-> Condition k t v
constructFull context degree volume rules rem [] = 
	construct context degree volume rules rem
constructFull context degree volume rules rem conds = res where
	(nDegree, nVolume, proj, nRem) = mergeConditions degree volume rem conds
	nRules = Map.delete Volume.empty $ Map.mapKeysWith mergeRules proj rules
	res = construct context nDegree nVolume nRules nRem
	
-- Constructs a condition from a degree and a single rule.
constructSimple :: Int -> Rule k t v (Either v Int) -> Condition k t v
constructSimple degree rule = Condition {
	degree = degree, volume = Volume.single,
	rules = Map.singleton Volume.single rule }



-- A condition that is always satisfied.
always :: Condition k t v
always = Condition {
	degree = 0, volume = Volume.single,
	rules = Map.empty }
	
-- A condition that is never satisfied.
never :: Condition k t v
never = Condition {
	degree = 0, volume = Volume.empty,
	rules = Map.empty }

-- Determines whether the given condition is always satisfied.
isAlways :: Condition k t v -> Bool
isAlways cond = not (Volume.null $ volume cond) && Map.null (rules cond)

-- Determines whether the given condition is never satisfied.
isNever :: Condition k t v -> Bool
isNever cond = Volume.null $ volume cond

-- Constructs a condition that is satisfied exactly when the given constraint is
-- satisfied.
simple :: (Ord v, Formula k) => k v -> Condition k t v
simple cons = constructSimple 0 (Map.empty, [fmap Left cons])

-- Constructs a condition that is satisfied exactly when all of the given constraint is
-- satisfied.
simples :: (Ord v, Formula k) => [k v] -> Condition k t v
simples cons = constructSimple 0 (Map.empty, List.map (fmap Left) cons)

-- Constructs a condition that is satisfied exactly when the given substitution is in
-- effect.
solution :: (Ord v, Formula t) => Map v (t v) -> Condition k t v
solution subs = constructSimple 0 (Map.map (fmap Left) subs, [])

-- Constructs a condition that is satisfied exactly when the given substitution is in
-- effect.
solutionFromList :: (Ord v, Formula t) => [(v, t v)] -> Condition k t v
solutionFromList subs = solution $ Map.fromList subs

-- Applies a one-to-one mapping to the variables in a condition.
map :: (Ord v, Ord n, Formula k, Formula t) => (v -> n)
	-> Condition k t v -> Condition k t n
map m cond = res where
	mapRule (subs, cons) =
		(Map.mapKeys m $ Map.map (fmap $ either (Left . m) Right) subs,
		List.map (fmap $ either (Left . m) Right) cons)
	res = Condition {
		degree = degree cond, volume = volume cond,
		rules = Map.map mapRule (rules cond) }
		
-- Applies a substitution to a constraint.
sub :: (Ord v, Ord n, Constraint r k t) => r -> (v -> t n)
	-> Condition k t v -> Condition k t n
sub context m cond = res where
	mapVar (Left x) = fmap Left $ m x
	mapVar (Right x) = tvar context (Right x)
	conjRule (subs, cons) = res where
		conds' = Map.foldWithKey (\v t a ->
			ceq context (fmap Left $ m v) (tsub context mapVar t) : a) [] subs
		conds = List.foldl (\a cons -> csub context mapVar cons : a) conds' cons
		res = conjunction context conds
	conds = List.map (\(v, r) -> (v, conjRule r)) $ Map.toList $ rules cond
	res = constructFull context (degree cond) (volume cond) Map.empty [] conds
	
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
existsRightInt :: (Ord v, Formula k, Formula t) => Int -> Condition k t (Either v Int)
	-> Condition k t v
existsRightInt bound cond = res where
	mapVar (Left x) = Left x
	mapVar (Right x) = Right (degree cond + x)
	mapRule (subs, cons) = res where
		nSubs = Map.mapKeysMonotonic fromJust $ Map.delete Nothing $
			Map.mapKeys (either Just (const Nothing)) $
			Map.map (fmap $ either mapVar Right) subs
		nCons = List.map (fmap $ either mapVar Right) cons
		res = if List.null cons && Map.null nSubs then Nothing else Just (nSubs, nCons)
	nRules = Map.mapMaybe mapRule (rules cond)
	res = if Map.size nRules < Map.size (rules cond)
		then prune (degree cond + bound) (volume cond) nRules
		else Condition { degree = degree cond + bound,
			volume = volume cond, rules = nRules }

-- Computes the conjunction of many conditions.
conjunction :: (Ord v, Constraint r k t) => r -> [Condition k t v] -> Condition k t v
conjunction _ [] = always
conjunction _ [cond] = cond
conjunction _ (cond : _) | isNever cond = never
conjunction context (cond : rem) | isAlways cond = conjunction context rem
conjunction context (cond : rem) = res where
	pushCondition Nothing _ = Nothing
	pushCondition (Just state) cond | isAlways cond = Just state
	pushCondition (Just _) cond | isNever cond = Nothing
	pushCondition (Just (degree', volume', ammends)) cond = res where
		nDegree = degree' + degree cond
		offsetVar = either Left (Right . (degree' +))
		(nVolume, proj) = Volume.product volume' (volume cond)
		nAmmends' = List.map (List.map (\(v, r) -> (proj v (volume cond), r))) ammends
		cMapRule (subs, cons) = (Map.mapKeysMonotonic Left $
			Map.map (fmap offsetVar) subs, List.map (fmap offsetVar) cons)
		cAmmends = List.map (\(v, r) -> (proj volume' v, cMapRule r)) $ 
			Map.assocs (rules cond)
		nAmmends = cAmmends : nAmmends'
		res = Just (nDegree, nVolume, nAmmends)
	cMapRule (subs, cons) = (Map.mapKeysMonotonic Left subs, cons)
	cAmmends = List.map (\(v, r) -> (v, cMapRule r)) $ Map.assocs (rules cond)
	state = Just (degree cond, volume cond, [cAmmends])
	res = case List.foldl pushCondition state rem of
		Just (nDegree, nVolume, nAmmends) ->
			construct context nDegree nVolume Map.empty nAmmends
		Nothing -> never

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
		nRules' = Map.mapKeys lProj rules'
		cRules = Map.mapKeys rProj (rules cond)
		nRules = Map.unionWith undefined nRules' cRules
		res = Just (nDegree, nVolume, nRules)
	state = Just (degree cond, volume cond, rules cond)
	res = case List.foldl pushCondition state rem of
		Just (nDegree, nVolume, nRules) -> Condition {
			degree = nDegree, volume = nVolume, rules = nRules }
		Nothing -> always

-- Constructs a condition that is satisfied exactly when both of the given conditions
-- are satisfied.
infixl 3 &&^
(&&^) :: (Ord v, Constraint () k t) => 
	Condition k t v -> Condition k t v -> Condition k t v
(&&^) x y = conjunction () [x, y]
	
-- Constructs a condition that is satisfied exactly when either of the given conditions
-- are satisfied.
infixl 2 ||^
(||^) :: (Ord v) => Condition k t v -> Condition k t v -> Condition k t v
(||^) x y = disjunction [x, y]

-- Constructs a condition that is satisfied exactly when the given terms are equivalent.
infix 4 ==^
(==^) :: (Ord v, Constraint () k t) => t v -> t v -> Condition k t v
(==^) x y = ceq () x y
		
-- Refines the constraints in a condition.
bind :: (Ord v, Constraint r k t) => r -> (forall n. (Ord n) => k n -> Condition k t n)
	-> Condition k t v -> Condition k t v
bind context m cond = res where
	stripRule (subs, _) | Map.null subs = Nothing
	stripRule (subs, _) = Just (subs, [])
	conjBindRule (_, cons) = conjunction context $ List.map m cons
	stripRules = Map.mapMaybe stripRule (rules cond)
	bindConds = List.map (\(v, r) -> (v, conjBindRule r)) $ Map.toList $ rules cond
	res = constructFull context (degree cond) (volume cond) stripRules [] bindConds

-- Reinterprets the given condition as a disjunction of a maximal set of solutions and
-- a non-solution condition. Note that returned solutions can reference existentially-
-- quantified variables.
extract :: (Ord v) => Condition k t v
	-> (Int, [Map v (t (Either v Int))], Condition k t v)
extract cond | (Volume.null $ volume cond) = (0, [], never)
extract cond | Map.null (rules cond) = (0, [Map.empty], never)
extract cond = res where
	extractIn volume _ _ | Volume.null volume = (Volume.empty, [])
	extractIn volume subs [] = (volume, [subs])
	extractIn volume subs ((rVolume, (rSubs, [])) : rem) = res where
		iSubs = Map.unionWith undefined subs rSubs
		(aVolume, aSubs) = extractIn (Volume.intersection volume rVolume) iSubs rem
		(bVolume, bSubs) = extractIn (Volume.difference volume rVolume) subs rem
		res = (Volume.union aVolume bVolume, aSubs ++ bSubs)
	extractIn volume subs ((rVolume, _) : rem) = res where
		res = extractIn (Volume.difference volume rVolume) subs rem
	(pVolume, subs) = extractIn (volume cond) Map.empty (Map.toList $ rules cond)
	(nVolume, proj) = Volume.cut (volume cond) pVolume
	nRules = Map.delete Volume.empty $ Map.mapKeysWith mergeRules proj (rules cond)
	nCond = Condition { degree = degree cond, volume = nVolume, rules = nRules }
	res = (degree cond, subs, nCond)
	
-- Reinterprets the given condition as a disjunction of a maximal set of solutions and
-- a non-solution condition.
extractToList :: (Ord v) => Condition k t v
	-> (Int, [[(v, t (Either v Int))]], Condition k t v)
extractToList cond = res where
	(degree, subs, nCond) = extract cond
	nSubs = List.map Map.toList subs
	res = (degree, nSubs, nCond)

-- Determines whether the given condition has a solution.
isSolvable :: (Ord v) => Condition k t v -> Bool
isSolvable cond = not $ List.null $ (\(_, s, _) -> s) $ extract cond

-- Merges equivalent constraints and substitutions within a condition. This should not
-- change the meaning of a condition, but will likely reduce its complexity.
coalesce :: (Ord v, Ord (k (Either v Int)), Ord (t (Either v Int)))
	=> Condition k t v -> Condition k t v
coalesce cond | (Volume.null $ volume cond) = never
coalesce cond | Map.null (rules cond) = always
coalesce cond = res where
	(solMap, consMap) = Map.foldrWithKey (\vol (sols, cons) (solMap, consMap) ->
		(Map.foldrWithKey (\var term accum ->
			Map.insertWith Volume.union (var, term) vol accum) solMap sols,
		List.foldl (\accum cons ->
			Map.insertWith Volume.union cons vol accum) consMap cons))
		(Map.empty, Map.empty) (rules cond)
	nRules' = Map.foldrWithKey (\(var, term) vol accum ->
		Map.insertWith mergeRules vol (Map.singleton var term, []) accum)
		Map.empty solMap
	nRules = Map.foldrWithKey (\cons vol accum ->
		Map.insertWith mergeRules vol (Map.empty, [cons]) accum)
		nRules' consMap
	res = optimize $ prune (degree cond) (volume cond) nRules