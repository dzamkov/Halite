{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Halisp.Term (Term)
import qualified Halisp.Term as Term
import Halisp.System (System)
import qualified Halisp.System as System
import qualified Halisp.Context as Context
import qualified Halisp.Parser as Parser
import qualified Halisp.Converter as Converter

term = Term.map undefined . Parser.parse Parser.term

system = fromJust $ System.fromList $ map (Parser.parse Parser.rule) $ [
	"Double[Pre[x, y]] = Pre[x, Pre[x, Double[y]]]",
	"Double[Nil] = Nil",
	"B = D"]
internal = System.source system
context = Internal.context $ internal
refine :: (Ord v) => Internal.Condition v -> Internal.Condition v
refine = Internal.refine $ internal

query :: (Ord v) => QueryT String v IO [Integer]
query = do
	k <- Interpreter.load [0 :: Integer .. 3]
	-- r <- Query.term (app "Double" [var k])
	Interpreter.read k
	
res = Query.eval query system

main = return ()