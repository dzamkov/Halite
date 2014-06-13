{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Halisp.Converter (
	Converter (..),
	Convertible (..)
) where

import Halisp.Term (Term)
import qualified Halisp.Term as Term
import Halisp.Context (Context)
import qualified Halisp.Context as Context
import qualified Halisp.Parser as Parser
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import qualified Data.List as List
import Control.Monad.State

-- Contains state information needed to convert to and from parser terms.
data Converter u s = Converter {

	-- Maps string symbols, along with their dimension, to term symbols.
	symbols :: Map (String, Int) (Either u s),
	
	-- An infinite list of unused arbitrary values to be assigned to new symbols as they
	-- are encountered.
	free :: [u] }
	
-- Identifies a possible mapping between parser and system objects.
class Convertible u s a b where
	convert :: Context u s -> a -> State (Converter u s) b

instance Convertible u s Parser.Term (Term u s String) where
	convert _ (Parser.Var var) = return $ Term.var var
	convert context (Parser.App sym args) = do
		let dim = List.length args
		converter <- get
		nArgs' <- forM args (convert context)
		case Map.lookup (sym, dim) $ symbols converter of
			Just (Right nSym) -> return $ 
				Context.reduce context nSym $ Vector.fromList nArgs'
			Just (Left nSym) -> return $ Term.comFromList (Term.arb nSym : nArgs')
			Nothing -> do
				let (nSym : nFree) = free converter
				put $ converter { 
					symbols = Map.insert (sym, dim) (Left nSym) $ symbols converter,
					free = nFree }
				return $ Term.comFromList (Term.arb nSym : nArgs')
	convert _ (Parser.Int _) = undefined