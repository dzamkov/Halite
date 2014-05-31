{-# LANGUAGE MultiParamTypeClasses #-}
module Halisp.System.Internal (
	Context (..),
	Term (..),
	Cons (..),
	System (..),
	Condition,
	empty,
	reduce,
	trefers,
	tmap,
	tvars,
	summary,
	getMainOps,
	getSymmOp,
	getPostOp,
	getPostArbOp,
	resolve,
	refine,
	identity,
	fromList
) where

import Prelude hiding (reverse)
import Prelude.Extras (Eq1 (..), Ord1 (..))
import Halisp.Condition ((||^))
import qualified Halisp.Condition as Condition
import Data.Set (Set)
import qualified Data.Set as Set
import Halisp.System.HalfMatrix (HalfMatrix)
import qualified Halisp.System.HalfMatrix as HalfMatrix
import Data.Vector (Vector, (!))
import qualified Data.Vector as Vector
import qualified Data.List as List

-- Describes a set of symbols, along with reductions between terms using those symbols.
data Context = Context {

	-- The symbols defined in this context, along with their expected number of arguments.
	symbols :: Vector Int } deriving (Show)
	
-- An empty context.
empty = Context { symbols = Vector.empty }

-- Reduces an applicative term (with all arguments reduced) within a context.
reduce :: (Ord v) => Context -> Int -> Vector (Term v) -> Term v
reduce _ sym args = App sym args

-- A term, as defined internally by a system. 
data Term v
	= Var v
	| Arb Int
	| App Int (Vector (Term v))
	| Com (Vector (Term v)) 
	deriving (Eq, Ord, Show)

instance Eq1 Term where
	(==#) = (==)
	
instance Ord1 Term where
	compare1 = compare
	
instance Condition.Formula Term where
	frefers p t = trefers p t
	fmap m t = tmap m t

instance Condition.Term Context Term where
	tsub _ m (Var v) = m v
	tsub _ _ (Arb u) = Arb u
	tsub c m (App sym args) = reduce c sym (Vector.map (Condition.tsub c m) args)
	tsub c m (Com elems) = Com $ Vector.map (Condition.tsub c m) elems
	tvar _ v = Var v
	
-- Determines whether the given term refers to any variable for which the given predicate
-- is true.
trefers :: (v -> Bool) -> Term v -> Bool 
trefers p (Var v) = p v
trefers _ (Arb _) = False
trefers p (App _ args) = Vector.any (trefers p) args
trefers p (Com elems) = Vector.any (trefers p) elems

-- Applies a one-to-one mapping to the variables in a term.
tmap :: (v -> n) -> Term v -> Term n
tmap m (Var v) = Var (m v)
tmap _ (Arb u) = Arb u
tmap m (App sym args) = App sym $ Vector.map (tmap m) args
tmap m (Com elems) = Com $ Vector.map (tmap m) elems

-- Gets the set of all variables referenced in a term.
tvars :: (Ord v) => Term v -> Set v
tvars (Var v) = Set.singleton v
tvars (Arb _) = Set.empty
tvars (App _ args) = Vector.foldl (\a t -> Set.union a (tvars t)) Set.empty args
tvars (Com elems) = Vector.foldl (\a t -> Set.union a (tvars t)) Set.empty elems

-- A constraint, as defined internally by a system. All constraints test whether an
-- applicative term is equal to an arbitrary term.
data Cons v = Eq (Maybe Int) Int (Vector (Term v)) (Term v) deriving (Eq, Ord, Show)

instance Eq1 Cons where
	(==#) = (==)

instance Ord1 Cons where
	compare1 = compare

instance Condition.Formula Cons where
	frefers p (Eq _ sym args other) = Vector.any (trefers p) args || trefers p other
	fmap m (Eq prv sym args other) = Eq prv sym (Vector.map (tmap m) args) (tmap m other)
	
instance Condition.Constraint Context Cons Term where
	csub c m (Eq prv sym args other) = ceq prv c
		(reduce c sym $ Vector.map (Condition.tsub c m) args) 
		(Condition.tsub c m other)
	ceq = ceq Nothing

-- Gets a condition that is satisfied when the two given terms are equal when an operation
-- from 'x' to symbol 'prv' is disallowed.
ceq prv c x y = res where
	ceqVar v t | Condition.frefers (== v) t = case t of
		App sym args -> Condition.simple $ Eq Nothing sym args (Var v)
		_ -> Condition.never
	ceqVar v t = Condition.solution [(v, t)]
	res = case (x, y) of
		(Var x, Var y) -> if x == y then Condition.always
			else Condition.solution [(x, Var y)]
		(Var v, t) -> ceqVar v t
		(t, Var v) -> ceqVar v t
		(App sym args, other) -> Condition.simple $ Eq prv sym args other
		(other, App sym args) -> Condition.simple $ Eq Nothing sym args other
		(Arb x, Arb y) -> if x == y then Condition.always else Condition.never
		(Com x, Com y) -> if Vector.length x /= Vector.length y then Condition.never
			else Condition.conjunction c $ Vector.toList $
				Vector.zipWith (Condition.ceq c) x y
		_ -> Condition.never

-- A specialized condition as used within systems.
type Condition v = Condition.Condition Cons Term v

-- Describes an "extensible" equivalence relation of terms in a context.
-- The "extensible" property refers to a pair of application terms being considered 
-- equivalent if they have the same symbol, and each corresponding argument is equivalent.
data System = System {

	-- The context for this system.
	context :: Context,
	
	-- Describes the main operations in this system. These determine when one applicative
	-- term can be transformed into another as an initial or intermediate operation in
	-- a sequence of operations.
	mainOps :: HalfMatrix (Condition (Either Int Int)),
	
	-- Describes the symmetric operations in this system. These are determined by main
	-- operations, and correspond to applications of an operation of a given symbol,
	-- immediately followed by the reverse operation.
	symmOps :: Vector (Condition (Either Int Int)),
	
	-- Describes the post-operations in this system. These determine when one applicative
	-- term can be transformed into another as the final operation in a sequence of
	-- operations.
	postOps :: HalfMatrix (Condition (Either Int Int)),
	
	-- Describes the arbitrary post-operations in this system. These determine when an
	-- applicative can be transformed into a arbitrary term as the final operation in a
	-- sequence of operations.
	postArbOps :: Vector (Condition (Maybe Int)) }
	
-- Reverses a condition (useful for half-matrix symmetry).
reverse :: (Ord a, Ord b) => Condition (Either a b) -> Condition (Either b a)
reverse cond = Condition.map (either Right Left) cond

-- Combines two conditions, representing operations, into one.
merge :: (Ord a, Ord b) => Context -> Int
	-> Condition (Either a Int) 
	-> Condition (Either Int b)
	-> Condition (Either a b)
merge context dim a b = Condition.existsRightInt dim $ Condition.conjunction context $
	[Condition.map (either (Left . Left) Right) a,
	Condition.map (either Right (Left . Right)) b]

-- Gets a summary of the operations contained in a system.
summary :: System -> ([(Int, Int)], [Int], [(Int, Int)], [Int])
summary system = res where
	collectSyms a i c | Condition.isNever c = a
	collectSyms a i _ = i : a
	res = (HalfMatrix.ifold collectSyms [] $ mainOps system,
		Vector.ifoldl collectSyms [] $ symmOps system,
		HalfMatrix.ifold collectSyms [] $ postOps system,
		Vector.ifoldl collectSyms [] $ postArbOps system)

-- Gets all main operations for the given symbol within a system.
getMainOps :: System -> Int -> [(Int, Condition (Either Int Int))]
getMainOps system = (Vector.!) $ 
	Vector.accum (flip (:)) (Vector.replicate (HalfMatrix.size $ mainOps system) []) $
	HalfMatrix.ifold (\a (x, y) c ->
		if Condition.isNever c then a
		else if x == y then (x, (x, c)) : a
		else (x, (y, c)) : (y, (x, reverse c)) : a) [] $ mainOps system
		
-- Gets an operation in the given system that corresponds to every possible application
-- of a main operation of a given symbol, immediately followed by its inverse. The obvious
-- identity operations that result will be removed.
getSymmOp :: System -> Int -> Condition (Either Int Int)
getSymmOp system sym = symmOps system ! sym

-- Gets all the post-operations between the given symbols within a system.	
getPostOp :: System -> Int -> Int -> Condition (Either Int Int)
getPostOp system xSym ySym = if xSym <= ySym
	then (HalfMatrix.!) (postOps system) (xSym, ySym)
	else reverse $ (HalfMatrix.!) (postOps system) (ySym, xSym)
		
-- Gets all the post-arbitrary-operations for the given symbol within a system.
getPostArbOp :: System -> Int -> Condition (Maybe Int)
getPostArbOp system sym = postArbOps system ! sym
		
-- Resolves a constraint within a system.
resolve :: (Ord v) => System -> Cons v -> Condition v
resolve system = res where
	sGetMainOps = getMainOps system
	apply context prv sym args oSym dim cond other = Condition.existsRightInt dim $
		Condition.conjunction context $
		[Condition.sub context (\v -> case v of
			Left i -> tmap Left (args ! i)
			Right i -> Var $ Right i) cond,
		Condition.simple $ Eq prv oSym
			(Vector.generate dim (Var . Right)) $
			tmap Left other]
	trans pSym sym args other = res where
		transOne (oSym, cond) | pSym == oSym = Condition.never
		transOne (oSym, cond) = apply (context system) (Just sym) sym args 
			oSym ((symbols $ context system) ! oSym) cond other
		res = List.map transOne $ sGetMainOps sym
	symm sym args other = apply (context system) Nothing sym args
		sym ((symbols $ context system) ! sym) (getSymmOp system sym) other
	res (Eq prv sym args other) = cond where
		pSym = case prv of
			Nothing -> -1
			Just pSym -> pSym
		conds''' = trans pSym sym args other
		conds'' = symm sym args other : conds'''
		appConds oSym oArgs = conds where
			conds' = Condition.sub (context system) (\v -> case v of
				Left i -> args ! i
				Right i -> oArgs ! i) (getPostOp system sym oSym) : conds''
			conds = if sym /= oSym then conds' else 
				(Condition.conjunction (context system) $
				Vector.toList $ Vector.zipWith (Condition.ceq $ context system)
				args oArgs) : conds'
		conds = case other of
			App oSym oArgs -> appConds oSym oArgs
			other -> Condition.sub (context system) (\v -> case v of
				Just i -> args ! i
				Nothing -> other) (getPostArbOp system sym) : conds''
		cond = Condition.disjunction conds
		
-- Refines a condition within a system.
refine :: (Ord v) => System -> Condition v -> Condition v
refine system = Condition.bind (context system) (resolve system)
	
-- A system where terms are equivalent iff they are the structurally the same.
identity :: System
identity = System { 
	context = empty,
	mainOps = HalfMatrix.empty,
	symmOps = Vector.empty,
	postOps = HalfMatrix.empty,
	postArbOps = Vector.empty }

-- Creates symmetric operations from the given main operations.
makeSymmOps :: Context
	-> HalfMatrix (Condition (Either Int Int))
	-> Vector (Condition (Either Int Int))
makeSymmOps context mainOps = res where
	apply oSym cond = merge 
		context (symbols context ! oSym)
		cond (reverse cond)
	res = Vector.generate (HalfMatrix.size mainOps) (\sym ->
		List.foldl (\a oSym -> a ||^ (apply oSym $
			HalfMatrix.symm id id reverse mainOps (sym, oSym)))
		Condition.never [0 .. HalfMatrix.size mainOps - 1])
	
-- Constructs the minimal system which contains the given equivalence rules. Variables
-- act as place-holders for any term. Returns Nothing if the system is degenerate.
fromList :: (Ord v) => Context -> [(Term v, Term v)] -> Maybe System
fromList context rules = res where
	insertRule Nothing _ = Nothing
	insertRule (Just state) (x, y) = res where
		insertArbRule _ var _ args | not (Vector.any (trefers (== var)) args) = Nothing
		insertArbRule (mainOps, postArbOps) var sym args = Just res where
			cond = Condition.existsRight (tvars (App sym args)) $
				Condition.conjunction context $ Vector.ifoldl (\a i t ->
					Condition.ceq context (Var $ Left $ Just i) (tmap (\v ->
						if v == var then Left Nothing
						else Right v) t) : a) 
					[] args
			nPostArbOps = (sym, cond) : postArbOps
			nMainOps = Vector.ifoldl (\a s d -> ((sym, s), 
				Condition.sub context (\v -> case v of
					Just i -> Var $ Left i
					Nothing -> App s $ Vector.generate d (Var . Right))
				cond) : a) mainOps (symbols context)
			res = (nMainOps, nPostArbOps)
		insertAppRule (mainOps, postArbOps) xSym xArgs ySym yArgs = Just res where
			vars = Set.union (tvars $ App xSym xArgs) (tvars $ App ySym yArgs)
			conjs m args accum = Vector.ifoldl (\a i t ->
				Condition.ceq context (Var $ Left $ m i) (tmap Right t) : a)
				accum args
			cond = Condition.existsRight vars $
				Condition.conjunction context $
				conjs Left xArgs $ conjs Right yArgs []
			nMainOps = ((xSym, ySym), cond) : mainOps
			res = (nMainOps, postArbOps)
		res = case (x, y) of
			(Var x, Var y) -> if x == y then Just state else Nothing
			(Var x, App sym args) -> insertArbRule state x sym args
			(App sym args, Var y) -> insertArbRule state y sym args
			(App xSym xArgs, App ySym yArgs) -> insertAppRule state xSym xArgs ySym yArgs
	symmetrize ((xSym, ySym), cond) = case compare xSym ySym of
		LT -> ((xSym, ySym), cond)
		EQ -> ((xSym, xSym), cond ||^ reverse cond)
		GT -> ((ySym, xSym), reverse cond)
	size = Vector.length $ symbols context
	create mainOps' postArbOps' = res where
		mainOps = HalfMatrix.accum (||^) (HalfMatrix.replicate size Condition.never) $
			List.map symmetrize mainOps'
		symmOps = makeSymmOps context mainOps
		postArbOps = Vector.accum (||^) (Vector.replicate size Condition.never) $
			postArbOps'
		res = System {
			context = context,
			mainOps = mainOps,
			symmOps = symmOps,
			postOps = HalfMatrix.replicate size Condition.never,
			postArbOps = postArbOps }
	res = case List.foldl insertRule (Just ([], [])) rules of
		Nothing -> Nothing
		Just (mainOps, postArbOps) -> Just $ create mainOps postArbOps