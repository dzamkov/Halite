{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Halisp.Term (Term (..), var, app)
import qualified Halisp.Term as Term
import Halisp.System (System)
import qualified Halisp.System as System
import qualified Halisp.System.Internal as Internal
import qualified Halisp.System.Term as ITerm
import Halisp.Query (QueryT, Query)
import qualified Halisp.Query as Query
import qualified Data.Vector as Vector
import qualified Halisp.Parser as Parser
import qualified Halisp.Condition as Condition
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Control.Monad.Trans
import Debug.Trace (trace)
import qualified Halisp.Interpreter as Interpreter

term = Term.map undefined . Parser.parse Parser.term

system = fromJust $ System.fromList $ map (Parser.parse Parser.rule) $ [
	"Double[Pre[x, y]] = Pre[x, Pre[x, Double[y]]]",
	"Double[Nil] = Nil",
	"B = D"]
context = Internal.context $ System.source system
	
query :: (Ord v) => QueryT String v IO [Integer]
query = do
	k <- Interpreter.load [0 :: Integer .. 3]
	-- r <- Query.term (app "Double" [var k])
	Interpreter.read k
	
res = Query.eval query system

main = return ()