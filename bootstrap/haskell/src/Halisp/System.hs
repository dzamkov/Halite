{-# LANGUAGE MultiParamTypeClasses #-}
module Halisp.System (
	System (..),
	identity,
	fromList
) where

import Halisp.Term (Term (..))
import qualified Halisp.Term as Term
import qualified Halisp.System.Term as STerm
import qualified Halisp.System.Internal as Internal
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import qualified Data.List as List

-- Describes an "extensible" equivalence relation of terms having a given symbol type.
data System s = System {

	-- A mapping of external symbols (along with their amount of arguments) to symbols
	-- internally used in the source system.
	symbols :: Map (s, Int) Int,

	-- The source system for this system.
	source :: Internal.System }

-- A system where terms are equivalent iff they are the structurally the same.
identity :: System s
identity = System { symbols = Map.empty, source = Internal.identity }

-- Constructs the minimal system which contains the given equivalence rules. Variables
-- act as place-holders for any term.
fromList :: (Ord s, Ord v) => [(Term s v, Term s v)] -> Maybe (System s)
fromList rules = res where
	(symMap, symbols, complexity) = Set.foldr (\i (m, s, c) -> 
		(Map.insert i c m, snd i : s, c + 1)) (Map.empty, [], 0) $
		List.foldl (\a (x, y) -> Set.union a $
		Set.union (Term.symbols x) (Term.symbols y)) Set.empty rules
	context = Internal.Context {
		Internal.symbols = Vector.reverse $ Vector.fromList symbols }
	m = (Map.!) symMap
	nRules = List.map (\(x, y) -> (STerm.load m context x, STerm.load m context y)) rules
	res = case Internal.fromList context nRules of
		Nothing -> Nothing
		Just source -> Just $ System { symbols = symMap, source = source }