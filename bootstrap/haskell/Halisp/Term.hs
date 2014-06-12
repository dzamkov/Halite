{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
module Halisp.Term (
	Term (..),
	vars,
	refers,
	map,
	var,
	app,
	appFromList,
	arb,
	com,
	comFromList,
	nat,
	sum,
	list,
	concat,
	concatParts,
	set,
	setFromList,
	union,
	sub,
	equal
) where

import Prelude hiding (map, sum, concat)
import Halisp.Condition (Condition)
import qualified Halisp.Condition as Condition
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import qualified Data.List as List

-- A value derived from a structured composition of values, variables and symbol
-- applications.
data Term u s v

	-- A term that can take the place of any other term.
	= Var v
	
	-- A term representing a symbol application; used to implement custom equivalences
	-- rules in System.
	| App s (Vector (Term u s v))
	
	-- A term with an arbitrary value.
	| Arb u
	
	-- A compound term. Two compound terms are equal if and only if all of their elements
	-- are equal.
	| Com (Vector (Term u s v))
	
	-- A term representing a natural number as the sum of a constant and a set of terms
	-- (multiplied by the given coefficients).
	| Nat Integer (Map (Term u s v) Integer)
	
	-- A term representing a list as a concatenation of elements (False) and lists (True).
	| List [(Bool, Term u s v)]
	
	-- A term representing a set as the union of a given set of elements and sets.
	| Set (Set (Term u s v)) (Set (Term u s v))
	deriving (Eq, Ord, Show)
	
-- A reduction that can be applied to applicative terms.
newtype Reduction u s = Reduction (forall v. (Ord v)
	=> s -> Vector (Term u s v) -> Term u s v)

instance (Ord u, Ord s) => Condition.Formula (Term u s) where
	fvars = vars
	frefers = refers
	fmap = map
	
instance (Ord u, Ord s) => Condition.Term () (Term u s) where
	tvar _ = var
	tsub _ = sub app

instance (Ord u, Ord s) => Condition.Term (Reduction u s) (Term u s) where
	tvar _ = var
	tsub (Reduction app) = sub app
	
-- Gets the set of variables referenced in a term, using an accumulator.
vars' :: (Ord v) => Set v -> Term u s v -> Set v
vars' accum (Var x) = Set.insert x accum
vars' accum (App _ args) = Vector.foldl vars' accum args
vars' accum (Arb _) = Set.empty
vars' accum (Com elems) = Vector.foldl vars' accum elems
vars' accum (Nat _ map) = Map.foldlWithKey (\a t _ -> vars' a t) accum map
vars' accum (List parts) = List.foldl (\a (_, t) -> vars' a t) accum parts
vars' accum (Set elems sets) = Set.foldl vars' (Set.foldl vars' accum elems) sets

-- Gets the set of variables referenced in a term.
vars :: (Ord v) => Term u s v -> Set v
vars = vars' Set.empty

-- Determines whether the given term references a variable for which the given predicate
-- returns true.
refers :: (v -> Bool) -> Term u s v -> Bool
refers p (Var x) = p x
refers p (App _ args) = Vector.any (refers p) args
refers p (Arb _) = False
refers p (Com elems) = Vector.any (refers p) elems
refers p (Nat _ map) = Map.foldlWithKey (\a t _ -> a || refers p t) False map
refers p (List parts) = List.any (refers p . snd) parts
refers p (Set elems sets) = anyRefers elems || anyRefers sets where
	anyRefers = Set.foldl (\a t -> a || refers p t) False

-- Applies a one-to-one mapping to the variables in a term.
map :: (Ord u, Ord s, Ord n) => (v -> n) -> Term u s v -> Term u s n
map m (Var x) = Var (m x)
map m (App sym args) = App sym $ Vector.map (map m) args
map _ (Arb x) = Arb x
map m (Com elems) = Com $ Vector.map (map m) elems
map m (Nat const terms) = Nat const $ Map.mapKeys (map m) terms
map m (List parts) = List $ List.map (\(b, t) -> (b, map m t)) parts
map m (Set elems sets) = Set (Set.map (map m) elems) (Set.map (map m) sets)

-- Constructs a variable term.
var :: v -> Term u s v
var = Var

-- Constructs an applicative term without reduction.
app :: s -> Vector (Term u s v) -> Term u s v
app = App

-- Constructs an applicative term without reduction.
appFromList :: s -> [Term u s v] -> Term u s v
appFromList sym args = app sym (Vector.fromList args)

-- Constructs an arbitrary term.
arb :: u -> Term u s v
arb = Arb

-- Constructs a compound term.
com :: Vector (Term u s v) -> Term u s v
com = Com

-- Constructs a compound term.
comFromList :: [Term u s v] -> Term u s v
comFromList = com . Vector.fromList

-- Constructs a term for a natural number.
nat :: Integer -> Term u s v
nat n | n < 0 = undefined
nat n = Nat n Map.empty

-- Constructs a term for a sum of terms (with coefficients) and a constant, with an
-- accumulator.
sum' :: (Ord u, Ord s, Ord v)
	=> Integer -> Map (Term u s v) Integer
	-> [(Term u s v, Integer)] -> Term u s v
sum' const accum [] = Nat const accum
sum' const accum ((Nat hConst hMap, hCoeff) : tail) = sum'
	(const + hConst * hCoeff) (Map.unionWith (+) accum (Map.map (* hCoeff) hMap)) tail

-- Constructs a term for a sum of terms (with coefficients) and a constant.
sum :: (Ord u, Ord s, Ord v) => Integer -> [(Term u s v, Integer)] -> Term u s v
sum const = sum' const Map.empty

-- Constructs a term for a list.
list :: [Term u s v] -> Term u s v
list items = List $ List.map (\i -> (False, i)) items

-- Constructs a term for a concatenation of lists.
concat :: [Term u s v] -> Term u s v
concat lists = List $ List.concat $ List.map (\t -> case t of
	List parts -> parts
	term -> [(True, term)]) lists
	
-- Constructs a term for the concatenation of list parts. An item with a tag of True will
-- be interpreted as a list while an item with a tag of False will be interpreted as
-- an item.
concatParts :: [(Bool, Term u s v)] -> Term u s v
concatParts parts = List $ List.concat $ List.map (\i -> case i of
	(True, List parts) -> parts
	part -> [part]) parts
	
-- Constructs a term for a set.
set :: Set (Term u s v) -> Term u s v
set elems = Set elems Set.empty

-- Constructs a term for a set.
setFromList :: (Ord u, Ord s, Ord v) => [Term u s v] -> Term u s v
setFromList = set . Set.fromList

-- Constructs a term for a union, with an accumulator.
union' :: (Ord u, Ord s, Ord v)
	=> Set (Term u s v) -> Set (Term u s v)
	-> [Term u s v] -> Term u s v
union' elems sets [] = Set elems sets
union' elems sets ((Set hElems hSets) : tail) =
	union' (Set.union elems hElems) (Set.union sets hSets) tail
union' elems sets (hSet : tail) = union' elems (Set.insert hSet sets) tail

-- Constructs a term for a union.
union :: (Ord u, Ord s, Ord v) => [Term u s v] -> Term u s v
union = union' Set.empty Set.empty

-- Applies a substitution to a term, using the given function to reduce applicative terms.
sub :: (Ord u, Ord s, Ord n)
	=> (s -> Vector (Term u s n) -> Term u s n)
	-> (v -> Term u s n)
	-> Term u s v -> Term u s n
sub app m (Var x) = m x
sub app m (App sym args) = app sym $ Vector.map (sub app m) args
sub _ _ (Arb x) = Arb x
sub app m (Com elems) = com $ Vector.map (sub app m) elems
sub app m (Nat const terms) = sum const $
	List.map (\(t, c) -> (sub app m t, c)) $ Map.toList terms
sub app m (List parts) = concatParts $ List.map (\(b, t) -> (b, sub app m t)) parts
sub app m (Set elems sets) = union' (Set.map (sub app m) elems) Set.empty $
	List.map (sub app m) $ Set.toList sets
	
-- Constructs a condition that is satisfied when the two given terms are equivalent,
-- provided a function to construct a condition for when an applicative term is
-- equivalent to an arbitrary term.
equal :: (Ord u, Ord s, Ord v, Condition.Constraint r k (Term u s)) => r
	-> (s -> Vector (Term u s v) -> Term u s v -> Condition k (Term u s) v)
	-> Term u s v -> Term u s v -> Condition k (Term u s) v
equal context app x y = case (x, y) of
	(Var x, y) | not (refers (== x) y) -> Condition.solutionFromList [(x, y)]
	(x, Var y) | not (refers (== y) x) -> Condition.solutionFromList [(y, x)]
	(App sym args, y) -> app sym args y
	(x, App sym args) -> app sym args x
	(Arb x, Arb y) | x == y -> Condition.always
	(Com xElems, Com yElems) -> Condition.conjunction context $ Vector.toList $
		Vector.zipWith (Condition.ceq context) xElems yElems
	(Nat _ _, Nat _ _) -> undefined
	(List _, List _) -> undefined
	(Set _ _, Set _ _) -> undefined
	_ -> Condition.never