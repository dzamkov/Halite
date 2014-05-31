{-# LANGUAGE MultiParamTypeClasses #-}
module Halisp.Term (
	Term (..),
	var,
	app,
	refers,
	vars,
	varsToList,
	symbols,
	symbolsToList,
	map,
	sub
) where

import Prelude hiding (map)
import Prelude.Extras (Eq1 (..), Ord1 (..))
import Halisp.Condition (Condition)
import qualified Halisp.Condition as Condition
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.List as List

-- A relation of variables and values that acts as a value.
data Term s v = Var v | App s [Term s v] deriving (Eq, Ord, Show)

instance (Eq s) => Eq1 (Term s) where
	(==#) = (==)
	
instance (Ord s) => Ord1 (Term s) where
	compare1 = compare

instance (Ord s) => Condition.Formula (Term s) where
	frefers = refers
	fmap = map

instance (Ord s) => Condition.Term () (Term s) where
	tsub _ = sub
	tvar _ = var
	
-- Creates a term representing the given variable.
var :: v -> Term s v
var v = Var v

-- Creates a term representing an application of symbol.
app :: s -> [Term s v] -> Term s v
app sym args = App sym args
	
-- Determines whether the given term refers to any variable for which the given predicate
-- is true.
refers :: (v -> Bool) -> Term s v -> Bool
refers p (Var v) = p v
refers p (App _ args) = List.any (refers p) args

-- Gets the set of all variables referenced in a term.
vars :: (Ord v) => Term s v -> Set v
vars (Var v) = Set.singleton v
vars (App _ args) = List.foldl (\a t -> Set.union a (vars t)) Set.empty args

-- Gets the set of all variables referenced in a term, with no repeats.
varsToList :: (Ord v) => Term s v -> [v]
varsToList t = Set.toList $ vars t

-- Gets the set of all symbols referenced in a term, along with the number of arguments
-- they are applied to.
symbols :: (Ord s) => Term s v -> Set (s, Int)
symbols (Var _) = Set.empty
symbols (App sym args) = List.foldl (\a t -> Set.union a (symbols t))
	(Set.singleton (sym, List.length args)) args

-- Gets the set of all symbols referenced in a term, along with the number of arguments
-- they are applied to.
symbolsToList :: (Ord s) => Term s v -> [(s, Int)]
symbolsToList t = Set.toList $ symbols t

-- Applies a one-to-one mapping to the variables in a term.
map :: (v -> n) -> Term s v -> Term s n
map m (Var v) = Var (m v)
map m (App sym args) = App sym (List.map (map m) args)

-- Applies a substitution to the variables in a term.
sub :: (v -> Term s n) -> Term s v -> Term s n
sub m (Var v) = m v
sub m (App sym args) = App sym (List.map (sub m) args)