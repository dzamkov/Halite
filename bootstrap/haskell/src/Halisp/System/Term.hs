{-# LANGUAGE MultiParamTypeClasses #-}
module Halisp.System.Term (
	Term (..),
	var,
	app,
	appFromList,
	com,
	comFromList,
	arb,
	refers,
	vars,
	varsToList,
	map,
	sub,
	load
) where

import Prelude hiding (map)
import Halisp.System.Internal (Term (..))
import qualified Halisp.Term as External
import qualified Halisp.System.Internal as Internal
import qualified Halisp.Condition as Condition
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.List as List

var v = Var v
app c sym args = Internal.reduce c sym args
refers = Internal.trefers
map = Internal.tmap
vars :: (Ord v) => Term v -> Set v
vars = Internal.tvars
sub :: (Ord v, Ord n) => Internal.Context -> (v -> Term n) -> Term v -> Term n
sub c m t = Condition.tsub c m t

-- Creates a term representing an application of symbol.
appFromList :: (Ord v) => Internal.Context -> Int -> [Term v] -> Term v
appFromList c sym args = app c sym (Vector.fromList args)

-- Constructs a compound term.
com :: Vector (Term v) -> Term v
com elems = Com elems

-- Constructs a compound term.
comFromList :: [Term v] -> Term v
comFromList elems = com (Vector.fromList elems)

-- Constructs an arbitrary term.
arb :: Int -> Term v
arb value = Arb value

-- Gets the set of all variables referenced in a term, with no repeats.
varsToList :: (Ord v) => Term v -> [v]
varsToList t = Set.toList $ vars t

-- Converts an external term into an internal term.
load :: (Ord s, Ord v) => ((s, Int) -> Int) -> Internal.Context
	-> External.Term s v -> Term v
load m context (External.Var v) = var v
load m context (External.App sym args) = res where
	nSym = m (sym, List.length args)
	nArgs = Vector.map (load m context) $ Vector.fromList args
	res = app context nSym nArgs