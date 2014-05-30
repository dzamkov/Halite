{-# LANGUAGE FlexibleInstances #-}
module Halisp.Interpreter (
	Symbol (..),
	Object (..)
) where

import Prelude hiding (succ, read)
import Halisp.Term (Term (..), var, app)
import qualified Halisp.Term as Term
import Halisp.Query (QueryT, Query, QTerm)
import qualified Halisp.Query as Query

-- Identifies a type that can be used as the underlying symbol type for systems accepting
-- objects.
class (Ord s) => Symbol s where
	
	-- The symbol for adding one.
	succ :: s
	
	-- The symbol for zero.
	zero :: s
	
	-- The symbol for constructing a character from an integer.
	char :: s
	
	-- The symbol for prepending.
	pre :: s
	
	-- The symbol for an empty string.
	nil :: s
	
	-- The main symbol in a program.
	main :: s
	
	-- The symbol for monadic binding.
	bind :: s
	
	-- The symbol for a write operation.
	put :: s
	
	-- The symbol for a read operation.
	get :: s
	
instance Symbol String where
	pre = "Pre"
	nil = "Nil"
	char = "Char"
	succ = "Succ"
	zero = "Zero"
	main = "Main"
	bind = "Bind"
	put = "Put"
	get = "Get"

-- Identifies a type that can be converted to and from terms.
class Object a where

	-- Converts an object into a term.
	load :: (Symbol s, Ord v, Monad m) => a -> QueryT s v m (QTerm v)
	
	-- Reads an object from a term.
	read :: (Symbol s, Ord v, Monad m) => QTerm v -> QueryT s v m a

instance Object Integer where
	load x = do
		z <- Query.term (app zero [])
		Query.iter x succ z
	read = Query.uniter succ (\i t -> do
		z <- Query.term (app zero [])
		Query.equal t z
		return i)

instance Object Char where
	load x = do
		i <- load $ toInteger $ fromEnum x
		Query.term (app char [var i])
	read x = do
		i <- Query.var
		t <- Query.term (app char [var i])
		Query.equal x t
		r <- read i
		return $ toEnum $ fromInteger r

instance Object a => Object [a] where
	load [] = Query.term (app nil [])
	load (x : xs) = do
		head <- load x
		tail <- load xs
		Query.term (app pre [var head, var tail])
	read x = Query.branch [a, b] where
		a = do
			n <- Query.term (app nil [])
			Query.equal x n
			return []
		b = do
			head <- Query.var
			tail <- Query.var
			list <- Query.term (app pre [var head, var tail])
			Query.equal x list
			rHead <- read head
			rTail <- read tail
			Query.discard [head, tail]
			return (rHead : rTail)