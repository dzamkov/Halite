{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
module Halisp.System (
	Symbol (..),
	Term (..),
	Direction (..),
	Constraint (..),
	Condition,
	System (..),
	identity,
	resolve,
	refine
) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Vector (Vector, (!))
import qualified Data.Vector as Vector
import qualified Data.List as List
import qualified Halisp.Condition as Condition

-- Identifies a symbol type (within a context).
class (Ord s) => Symbol r s where

	-- Folds over all symbols (and their corresponding dimensions) in a context.
	sfold :: r -> (a -> s -> Int -> a) -> a -> a

	-- Gets the number of arguments expected by the given symbol.
	sdim :: r -> s -> Int

-- Identifies a type constructor for a term that can be used in a system.
class (Symbol r s, Condition.Term r t) => Term r t s | r t -> s where

	-- Constructs an applicative term.
	tapp :: (Ord v) => r -> s -> Vector (t v) -> t v

	-- Tries interpreting a term as an applicative term.
	tasApp :: (Ord v) => r -> t v -> Maybe (s, Vector (t v))
	
	-- Constructs a condition that is satisfied when the two given terms are equivalent,
	-- provided a function to construct a condition for when an applicative term is
	-- equivalent to an arbitrary term.
	teq :: (Ord v, Condition.Constraint r k t) => r
		-> (s -> Vector (t v) -> t v -> Condition.Condition k t v)
		-> t v -> t v -> Condition.Condition k t v

-- Describes the "direction" of an operation. Systems will arbitrarily assign a direction
-- to each transitive operation, insuring that each operation has the opposite direction
-- of its inverse.
data Direction = Forward | Backward deriving (Eq, Ord, Show)

-- A logical expression satisfied when an applicative term is equivalent to an arbitrary
-- term.
data Constraint t s v
	= Eq (Maybe (s, Direction)) s (Vector (t v)) (t v)
	deriving (Eq, Ord, Show)

instance (Condition.Formula t) => Condition.Formula (Constraint t s) where
	fvars (Eq _ _ args other) = Vector.foldl (\a t -> Set.union a $ Condition.fvars t)
		(Condition.fvars other) args
	frefers m (Eq _ _ args other) = Vector.any (Condition.frefers m) args ||
		Condition.frefers m other
	fmap m (Eq past sym args other) = Eq past sym (Vector.map (Condition.fmap m) args) $
		Condition.fmap m other

instance (Term r t s) => Condition.Constraint r (Constraint t s) t where
	csub context m (Eq past sym args other) = Condition.simple $ Eq past sym 
		(Vector.map (Condition.tsub context m) args) (Condition.tsub context m other)
	ceq context x y = teq context (\sym args other ->
		Condition.simple $ Eq Nothing sym args other) x y

-- A condition as defined by a system.
type Condition t s = Condition.Condition (Constraint t s) t
	
-- An "extensible" equivalence relation of terms having a given symbol type. The
-- extensible property means that if all the sub-terms of two terms are equivalent under
-- the system, the terms are equivalent. Note that systems only define equivalences for
-- applicative terms; equivalences for other types of terms are inherit in the Term
-- structure.
data System t s = System {

	-- Gets the transitive operations originating from the given symbol in a system. These
	-- conditions determine when an applicative term of that symbol can be transformed
	-- into another applicative term as as an initial or intermediate operation in a
	-- sequence of operations.
	transOps :: s -> [(Direction, s, Condition t s (Either Int Int))],
	
	-- Gets the symmetric operations in a system. These are determined by the transitive
	-- operations, and correspond to applications of a transitive operation of a given
	-- symbol, immediately followed by the inverse operation.
	symmOps :: s -> Condition t s (Either Int Int),

	-- Gets the post-operations in a system . These determine when one applicative
	-- term can be transformed into another as the final operation in a sequence of
	-- operations.
	postOps :: s -> s -> Condition t s (Either Int Int),
	
	-- Gets the arbitrary post-operations in a system. These determine when an applicative
	-- term can be transformed into a arbitrary term as the final operation in a
	-- sequence of operations.
	postArbOps :: s -> Condition t s (Maybe Int) }
	
-- A system that considers terms equivalent if and only if they are structurally the same.
identity :: System t s
identity = System {
	transOps = (\_ -> []),
	symmOps = (\_ -> Condition.never),
	postOps = (\_ _ -> Condition.never),
	postArbOps = (\_ -> Condition.never) }

-- Resolves a constraint within a system.
resolve :: (Ord v, Term r t s) => r -> System t s -> Constraint t s v -> Condition t s v
resolve context system (Eq past sym args other) = res where
	apply past args cond oSym = Condition.existsRightInt (sdim context oSym) $
		Condition.conjunction context $
		[Condition.sub context (\v -> case v of
			Left i -> Condition.fmap Left (args ! i)
			Right i -> Condition.tvar context $ Right i) cond,
		Condition.simple $ Eq past oSym
			(Vector.generate (sdim context sym) (Condition.tvar context . Right)) $
			Condition.fmap Left other]
	tran accum = List.foldl (case past of
			Just (pSym, pDir) -> (\a (oDir, oSym, cond) ->
				if pDir /= oDir && pSym == oSym then a
				else apply (Just (sym, oDir)) args cond oSym : a)
			Nothing -> (\a (oDir, oSym, cond) ->
				apply (Just (sym, oDir)) args cond oSym : a))
		accum $ transOps system sym
	symm accum = apply Nothing args (symmOps system sym) sym : accum
	post accum = case tasApp context other of
		Just (oSym, oArgs) -> (if sym /= oSym then id
			else ((Condition.conjunction context $ Vector.toList $
				Vector.zipWith (Condition.ceq context) args oArgs) :)) $
			(Condition.sub context (\v -> case v of
				Left i -> args ! i
				Right i -> oArgs ! i) $ postOps system sym oSym) : accum
		Nothing -> Condition.sub context (\v -> case v of
			Just i -> args ! i
			Nothing -> other) (postArbOps system sym) : accum
	res = Condition.disjunction $ post $ symm $ tran []
	
-- Refines a condition within a system.
refine :: (Ord v, Term r t s) => r -> System t s -> Condition t s v -> Condition t s v
refine context system = Condition.bind context (resolve context system)

-- Constructs the minimal system that includes the given equivalences. This assumes that
-- in the second list of equivalences between applicative terms and variables, the
-- applicative term references the variable. Otherwise, the system would be degenerate.
fromLists :: (Ord v, Term r t s) => r
	-> [(s, Vector (t v), s, Vector (t v))]
	-> [(s, Vector (t v), v)]
	-> System t s
fromLists context appApp appArb = res where
	conjs m args accum = Vector.ifoldl (\a i t -> (m i, t) : a) accum args
	appAppConds = List.map (\(xSym, xArgs, ySym, yArgs) -> (xSym, ySym,
		Condition.solution $ conjs Right xArgs $ conjs Left yArgs [])) appApp
	appArbConds = List.map (\(sym, args, var) -> (sym, Condition.solution $
		conjs Just args [(Nothing, Condition.tvar context var)])) appArb
	transOps sym = (flip $ List.foldl (\a (xSym, ySym, cond) ->
			(if sym == xSym then ((Forward, ySym, cond) :) else id) $
			(if sym == ySym then ((Backward, xSym, Condition.flip cond) :) else id) $ a))
		appAppConds $ (flip $ List.foldl (\a (aSym, cond) ->
			(if sym /= aSym then id else sfold context (\a tSym dim ->
				(Forward, tSym, Condition.sub context (\v -> case v of
					Just i -> Condition.tvar context $ Left i
					Nothing -> tapp context tSym $
						Vector.generate dim (Condition.tvar context . Right))
				cond) : a)) $
			((Backward, aSym, Condition.sub context (\v -> case v of
				Just i -> Condition.tvar context $ Right i
				Nothing -> tapp context sym $ 
					Vector.generate (sdim context sym) (Condition.tvar context . Left))
				cond) :) $ a))
		appArbConds $ []
	symmOps sym = Condition.disjunction $ List.foldl (\a (xSym, ySym, cond) ->
			(if sym == xSym then (Condition.joinInt context (sdim context ySym)
				cond (Condition.flip cond) :) else id) $
			(if sym == ySym then (Condition.joinInt context (sdim context xSym)
				(Condition.flip cond) cond :) else id) $ a)
		[] $ appAppConds
	postArbOps sym = Condition.disjunction $
		List.foldl (\a (aSym, cond) -> if sym == aSym then cond : a else a) [] appArbConds
	res = System {
		transOps = transOps,
		symmOps = symmOps,
		postOps = (\_ _ -> Condition.never),
		postArbOps = postArbOps }