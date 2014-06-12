{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Halisp.Context (
	Transformation (..),
	Context (..),
	reduce,
	simple
) where

import Halisp.Term (Term, Reduction (..))
import qualified Halisp.Term as Term
import Halisp.Condition (Condition)
import qualified Halisp.Condition as Condition
import Halisp.System (System)
import qualified Halisp.System as System
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import qualified Data.List as List

-- Describes a reduction rule that can be applied to certain forms of applications of a
-- given symbol.
data Transformation u s = Transformation {

	-- The number of variables in the pattern for this transformation.
	degree :: Int,

	-- Describes that pattern of symbol applications to which this transformation can be
	-- applied.
	args :: Vector (Term u s Int),
	
	-- The general form of the result of applying this transformation.
	target :: Term u s Int,
	
	-- Tries applying this transformation to an application of its associated symbol.
	-- The transformation may be applied multiple times.
	apply :: forall n. Vector (Term u s n) -> Maybe (Term u s n) }

-- Describes the basic properties and reductions of a set of symbols.
data Context u s = Context {

	-- Folds over all symbols (and their corresponding dimensions and transformations)
	-- defined in this context.
	fold :: forall a. (a -> s -> Int -> [Transformation u s] -> a) -> a -> a,
	
	-- Gets the dimension and transformations for a symbol in this context.
	info :: s -> (Int, [Transformation u s]) }

instance (Ord s) => System.Symbol (Context u s) s where
	sfold context m = fold context (\a sym dim _ -> m a sym dim)
	sdim context = fst . info context
	
instance (Ord u, Ord s) => Condition.Term (Context u s) (Term u s) where
	tvar _ = Term.var
	tsub context = Term.sub (reduce context)

-- Reduces an applicative term using the transformations in a context.
reduce :: Context u s -> s -> Vector (Term u s v) -> Term u s v
reduce context sym args = maybe (Term.app sym args) id $
	List.foldl (\accum trans -> maybe (apply trans args) Just accum) Nothing $ 
	snd $ info context sym

-- Constructs a simple context that contains no transformations.
simple :: (Ord s) => Map s Int -> Context u s
simple map = Context {
	fold = (\m accum -> Map.foldlWithKey (\a sym dim -> m a sym dim []) accum map),
	info = (\sym -> ((Map.!) map sym, [])) }