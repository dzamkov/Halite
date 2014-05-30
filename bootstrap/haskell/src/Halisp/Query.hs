{-# LANGUAGE RankNTypes #-}
module Halisp.Query (
	QueryT (..),
	Query,
	QTerm,
	eval,
	var,
	term,
	iter,
	equal,
	branch,
	uniter,
	discard
) where

import Prelude hiding (map)
import Halisp.Term (Term (..))
import qualified Halisp.Term as Term
import qualified Halisp.System.Term as STerm
import qualified Halisp.System.Internal as Internal
import qualified Halisp.Condition as Condition
import Halisp.System (System)
import qualified Halisp.System as System
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List
import Control.Monad.State
import Control.Monad.Identity
import Control.Monad (forM)

-- The mutable context for a query at any time.
data Context s v = Context {

	-- Assigns unique integers to each symbol that is used in the query, but not
	-- considered in the system. Applications of these symbols are encoded as compounds
	-- prefixed with an 'Arb' term of the corresponding symbol index.
	extra :: Map (s, Int) Int,
	
	-- The remaining free variables that can be used by the query.
	vars :: [v] } deriving (Show)

-- A term within a query.
newtype QTerm v = QTerm (Internal.Term v) deriving (Eq, Ord, Show)
	
-- Converts an a term into a query-internal term.
load :: (Ord s, Ord v) => System s -> Term s (QTerm v)
	-> State (Context s v) (Internal.Term v)
load _ (Var (QTerm t)) = return t
load system (App sym args) = res where
	symDim = (sym, List.length args)
	res = do
		nArgs <- forM args (load system)
		case Map.lookup symDim (System.symbols $ system) of
			Just nSym -> return $ STerm.appFromList
				(Internal.context $ System.source $ system) nSym nArgs
			Nothing -> do
				state <- get
				case Map.lookup symDim (extra state) of
					Just nSym -> return $ STerm.comFromList (STerm.arb nSym : nArgs)
					Nothing -> do
						let nSym = Map.size $ extra state
						put $ state { extra = Map.insert symDim nSym $ extra state }
						return $ STerm.comFromList (STerm.arb nSym : nArgs)	

-- A monad transformer for computations that inspect the equivalence relationships within
-- a system.
newtype QueryT s v m a = QueryT { run :: (Monad m) => System s
	-> Context s v -> Internal.Condition v
	-> m (Either 
		(Context s v, Internal.Condition v, a) 
		[(Context s v, Internal.Condition v, QueryT s v m a)]) }
	
-- A monad for computations that inspect the equivalence relationships within a system.
type Query s v = QueryT s v Identity

instance (Monad m) => Monad (QueryT s v m) where
	(>>=) x y = QueryT run' where
		run' system context cond = do
			r <- run x system context cond
			case r of
				Left (nContext, nCond, value) -> run (y value) system nContext nCond
				Right cases -> return $ Right $
					List.map (\(a, b, x) -> (a, b, x >>= y)) cases
	return value = QueryT run' where
		run' _ context cond = return (Left (context, cond, value))
		
instance (Monad m) => MonadPlus (QueryT s v m) where
	mplus x y = QueryT run' where
		run' system context cond = do
			rX <- run x system context cond
			rY <- run y system context cond
			return $ case (rX, rY) of
				(Left x, _) -> Left x
				(_, Left y) -> Left y
				(Right x, Right y) -> Right (x ++ y)
	mzero = QueryT run' where
		run' _ _ _ = return (Right [])

instance MonadTrans (QueryT s v) where
	lift x = QueryT run' where
		run' _ context cond = x >>= (\r -> return $ Left (context, cond, r))
		
instance (MonadIO m) => MonadIO (QueryT s v m) where
	liftIO = lift . liftIO
	
-- Evaluates a query, returning the result of the successful computation path, or Nothing
-- if no computation path has a solution.
eval :: (Ord s, Monad m) => (forall v. (Ord v) => QueryT s v m a)
	-> System s -> m (Maybe a)
eval query system = res where
	solve cases = case List.partition (\(_, c, _) -> Condition.isSolvable c) cases of
		(sol : a, b) -> Just (sol, b ++ a)
		([], cs) -> solve $ List.filter (\(_, c, _) -> not $ Condition.isNever c) $
			List.map (\(a, c, b) -> (a, Internal.refine (System.source system) c, b)) cs
	evalWith others query context cond = do
		r <- run query system context cond
		case r of
			Left (_, _, value) -> return $ Just value
			Right cases -> case solve (others ++ cases) of
				Just ((nContext, nCond, nQuery), nOthers) ->
					evalWith nOthers nQuery nContext nCond
				Nothing -> return $ Nothing
	context = Context { extra = Map.empty, vars = [0 ..] }
	res = evalWith [] query context Condition.always

-- Constructs a unrestricted variable within a query.
var :: (Ord s, Ord v, Monad m) => QueryT s v m (QTerm v)
var = QueryT run' where
	run' _ context cond = case vars context of
		(head : tail) -> return $ Left $
			(context { vars = tail }, cond, QTerm $ STerm.var head)

-- Loads a term into a query.
term :: (Ord s, Ord v, Monad m) => Term s (QTerm v) -> QueryT s v m (QTerm v)
term x = QueryT run' where
	run' system context cond = res where
		(nTerm, nContext) = runState (load system x) context
		res = return $ Left (nContext, cond, QTerm nTerm)

-- Constructs a term consisting of a certain number of iterated applications of the given
-- symbol to the given term.
iter :: (Ord s, Ord v, Monad m) => Integer -> s -> QTerm v -> QueryT s v m (QTerm v)
iter 0 sym t = return t
iter n sym t = do
	upper <- iter (n - 1) sym t
	term (Term.app sym [Var upper])

-- Restricts computation to cases where the given terms are equal.
equal :: (Ord v, Monad m) => QTerm v -> QTerm v -> QueryT s v m ()
equal (QTerm x) (QTerm y) = QueryT run' where
	run' system context cond = res where
		iContext = Internal.context $ System.source system
		nCond = Condition.conjunction iContext [cond, Condition.ceq iContext x y]
		res = return $ Right [(context, nCond, return ())]

-- A query that considers multiple computations with the assumption that at most one
-- has a solution.
branch :: (Monad m) => [QueryT s v m a] -> QueryT s v m a
branch [] = mzero
branch cases = List.foldl1 mplus cases

-- Deconstructs an iterated symbol application. The given inner query will be called for
-- the final (and possibly intermediate) steps of the application chain.
uniter :: (Ord s, Ord v, Monad m) => s -> (Integer -> QTerm v -> QueryT s v m a)
	-> QTerm v -> QueryT s v m a
uniter sym m t = uniter' [] 0 sym m t where
	uniter' vars n sym m t = branch [a, b] where
		a = do
			v <- var
			symApp <- term (Term.app sym [Var v])
			equal t symApp
			uniter' (v : vars) (n + 1) sym m v
		b = do
			nT <- var
			equal t nT
			discard vars
			m n nT

-- Removes a set of variables from consideration in a query, for performance reasons.
-- After discarding a variable, no term that references it may be used in a query
-- operation.
discard :: (Ord s, Ord v, Monad m) => [QTerm v] -> QueryT s v m ()
discard terms = QueryT run' where
	run' _ context cond = return $ Left (context, Condition.exists
		(List.foldl (\a (QTerm t) -> Set.union a (STerm.vars t)) Set.empty terms)
		cond, ())