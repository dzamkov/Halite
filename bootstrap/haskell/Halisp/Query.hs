{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Halisp.Query (
	Term (..),
	QueryT (..),
	Query,
	eval,
	var,
	app,
	equal,
	scoped
) where

import Prelude hiding (map)
import qualified Halisp.Condition as Condition
import Halisp.System (System)
import qualified Halisp.System as System
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.List as List
import Control.Monad.Trans
import Control.Monad.Identity
import Control.Monad (forM)

-- Describes the general form of the computation path of a query.
data Path c m s a

	-- A computation path that splits into two options.
	= forall p b. Branch (Path c m p b) (Path c m p b) (p -> b -> m (Result c m s a))
	
	-- A computation path that might fail, depending on a condition 'c'.
	| forall v. (Ord v) => Break (c v) (c v -> m (Result c m s a))
	
-- Describes the general form of the result of applying a query to a context/system.
data Result c m s a

	-- A result where there are no breaks or branches in the computation path.
	= Simple s a
	
	-- A result that has a complex computation path.
	| Complex (Path c m s a)
	
-- Binds the state and return value of a path.
pbind :: (Monad m)
	=> Path c m p b
	-> (p -> b -> m (Result c m s a))
	-> Path c m s a
pbind (Branch x y cont) m =
	Branch x y (\s v -> do
		res <- cont s v
		rbind res m)
pbind (Break c cont) m =
	Break c (\c -> do
		res <- cont c
		rbind res m)
	
-- Binds the state and return value of a result.
rbind :: (Monad m)
	=> Result c m p b
	-> (p -> b -> m (Result c m s a)) 
	-> m (Result c m s a)
rbind (Simple state value) m = m state value
rbind (Complex path) m = return $ Complex $ pbind path m
		
-- Constructs a result from a state and a value.
rreturn :: (Monad m) => s -> a -> m (Result c m s a)
rreturn state value = return $ Simple state value

-- Evaluates a path (with the given condition evaluation function) to get a result.
peval :: (Monad m)
	=>(forall v. (Ord v) => c v -> Maybe (Bool, c v))
	-> Path c m s a -> m (Maybe (Result c m s a))
peval eval (Branch x y cont) = do
	rX <- peval eval x
	rY <- peval eval y
	case (rX, rY) of
		(Nothing, Nothing) -> return Nothing
		(Nothing, Just rY) -> rbind rY cont >>= (return . Just)
		(Just rX, Nothing) -> rbind rX cont >>= (return . Just)
		(Just (Simple state value), Just _) -> cont state value >>= (return . Just)
		(Just _, Just (Simple state value)) -> cont state value >>= (return . Just)
		(Just (Complex nX), Just (Complex nY)) ->
			return $ Just $ Complex $ Branch nX nY cont
peval eval (Break cond cont) = case eval cond of
	Nothing -> return Nothing
	Just (False, nCond) -> return $ Just $ Complex $ Break nCond cont
	Just (True, nCond) -> cont cond >>= (return . Just)
		
-- A term that can be used in a query.
class (System.Term r t n) => Term q r t s n where

	-- Constructs an applicative term.
	tapp :: (Ord v) => r -> q -> s -> [v] -> (q, t v)
	
-- Encapsulates the state of a query computation path.
data State q t n v = State {

	-- The term-defined context used to convert query applicative terms into system/term
	-- applicative terms.
	converter :: q,
	
	-- An infinite list of variables that are not referenced in the condition for this
	-- state. When a new variable is needed, it is taken from this list.
	vars :: [v],
	
	-- Contains the variables for each scope in the state, ordered by distance from the
	-- current scope.
	scopes :: [Set v],
	
	-- The index of the current scope. The root scope is 0 and each inner scope is
	-- decremented by one. This is always one less than the length of the scopes list.
	scopeIndex :: Int,
	
	-- The condition under which this query path is successful.
	condition :: System.Condition t n v }

-- A monad transformer for computations that inspect the equivalence relationships within
-- a system.
newtype QueryT s v m a = QueryT {
	run :: forall q r t n. (Term q r t s n)
		=> r -> State q t n v
		-> m (Result (System.Condition t n) m (State q t n v) a) }

-- A monad for computations that inspect the equivalence relationships within a system.
type Query s v = QueryT s v Identity

instance (Monad m) => Monad (QueryT s v m) where
	(>>=) x y = QueryT (\context state -> do
		r <- run x context state
		rbind r (\nState value -> run (y value) context nState))
	return value = QueryT (\_ state -> rreturn state value)

instance MonadTrans (QueryT s v) where
	lift x = QueryT (\_ state -> x >>= (rreturn state))

instance (MonadIO m) => MonadIO (QueryT s v m) where
	liftIO = lift . liftIO
	
-- Evaluates a query with a system.
eval :: (Monad m, Term q r t s n)
	=> (forall v. (Ord v) => QueryT s v m a)
	-> r -> q -> System t n -> m a
eval query context converter system = res where
	iterate (Simple _ value) = return value
	iterate (Complex (Break cond cont)) = do
		r <- cont cond
		iterate r
	iterate (Complex path) = do
		r <- peval (\cond -> case cond of
			(Condition.isExtractable -> True) -> Just (True, cond)
			(Condition.isNever -> True) -> Nothing
			cond -> Just (False, System.refine context system cond)) path
		case r of
			Nothing -> undefined
			Just next -> iterate next
	state = State {
		converter = converter, 
		vars = [0 ..],
		scopes = [Set.empty],
		scopeIndex = 0,
		condition = Condition.always }
	res = do
		r <- run query context state
		iterate r


-- Gets a new variable in the current scope.
newVar :: (Ord v) => State q t n v -> (State q t n v, v)
newVar state = res where
	(var : nVars) = vars state
	(scope : oScopes) = scopes state
	res = (state {
		vars = nVars,
		scopes = (Set.insert var scope : oScopes) }, var)

-- Raises a variable from the given scope to the next higher scope.
raiseVar :: (Ord v) => Int -> v -> State q t n v -> State q t n v
raiseVar index var state = res where
	depth = scopeIndex state - index
	(lower, cur : next : higher) = List.splitAt depth $ scopes state
	nScopes = lower ++ (Set.delete var cur : Set.insert var next : higher)
	res = state { scopes = nScopes }

		
-- A query that returns an unrestricted variable term.
var :: (Monad m, Ord v) => QueryT s v m v
var = QueryT (\_ state ->
	let (nState, var) = newVar state
	in return $ Simple nState var)
	
-- A query that returns an applicative term.
app :: (Monad m, Ord v) => s -> [v] -> QueryT s v m v
app sym args = QueryT (\context state ->
	let (nConverter, term) = tapp context (converter state) sym args
	in let (nState, var) = newVar state
	in return $ Simple (nState {
		converter = nConverter,
		condition = Condition.restrictFromList context
			[(var, term)] $ condition state }) var)

-- Requires the given terms to be equivalent in the remainder of a query's computational
-- path.
equal :: (Monad m, Ord v) => v -> v -> QueryT s v m ()
equal x y = QueryT (\context state -> return $ Complex $ Break
	(Condition.conjunction context [condition state,
		Condition.solutionFromList [(x, Condition.tvar context y)]])
	(\nCond -> return $ Simple (state { condition = nCond }) ()))

-- Constructs a query that branches into multiple computation paths.
branch :: (Monad m, Ord v) => [QueryT s v m a] -> QueryT s v m a
branch = undefined

-- Constructs a scoped query. The inner query will operate on a different variable set
-- than the outer query, and conversion between the variable sets is explicit.
scoped :: forall s v m a. (Monad m, Ord v)
	=> (forall n. (Ord n)
		=> (v -> n)
		-> (n -> QueryT s n m v) 
		-> QueryT s n m a)
	-> QueryT s v m a
scoped inner = res where
	lowerState state = state {
		scopes = Set.empty : scopes state,
		scopeIndex = scopeIndex state + 1 }
	raiseState state = state {
		scopes = List.tail $ scopes state,
		scopeIndex = scopeIndex state - 1,
		condition = Condition.exists (List.head $ scopes state) $ condition state }
	raiseVarQuery index var = QueryT (\_ state ->
		return $ Simple (raiseVar index var state) var)
	res :: QueryT s v m a
	res = QueryT (\context state -> do
		let iState = lowerState state
		let iQuery = inner id (raiseVarQuery $ scopeIndex iState) :: QueryT s v m a
		r <- run iQuery context iState
		rbind r (\niState value -> return $ Simple (raiseState niState) value))