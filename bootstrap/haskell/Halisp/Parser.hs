module Halisp.Parser (
	Expression (..),
	parse,
	display,
	Term (..),
	Rule (..),
	Module (..)
) where

import Data.Char
import Text.ParserCombinators.Parsec hiding (parse)
import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec.Number (nat)

-- Identifies a type for a value that can be parsed and displayed.
class Expression a where

	-- A parser for an expression.
	parser :: CharParser () a
	
	-- Converts the expression into a string in such a way that it can be recovered by
	-- 'parse'.
	displays :: a -> ShowS
	
-- Applies a parser to a string with the assumption that there will be no parse error.
parse :: Expression a => String -> a
parse input = case P.parse parser "" input of
	Left err -> error $ "parse failed: " ++ show err
	Right value -> value
	
-- Converts an expression into a string.
display :: Expression a => a -> String
display exp = displays exp ""

-- A term that can be parsed and displayed.
data Term
	= Var String 
	| App String [Term]
	| Int Integer deriving (Eq, Ord)

instance Expression Term where
	parser = choice [do
		symOrVar <- many1 letter
		if isLower (head symOrVar) then return (Var symOrVar) else do
			option (App symOrVar []) $ between (char '[') (char ']') $ do
				args <- sepBy parser (spaces >> char ',' >> spaces)
				return (App symOrVar args), fmap Int nat]
	displays (Var x) = (x ++)
	displays (App sym []) = (sym ++)
	displays (App sym (arg : args)) = (sym ++) . ("[" ++) . displays arg .
		foldr (\arg a -> (", " ++) . displays arg . a) ("]" ++) args
	displays (Int val) = showsPrec 0 val
	
instance Show Term where
	showsPrec p term = showParen (p > 10) $ ("parse \"" ++) . displays term . ("\"" ++)

-- An equivalence rule between two terms.
data Rule = Rule Term Term deriving (Eq, Ord, Show)

instance Expression Rule where
	parser = do
		left <- parser
		spaces
		char '='
		spaces
		right <- parser
		return $ Rule left right
	displays (Rule left right) = displays left . (" = " ++) . displays right
	
-- A set of equivalences between terms.
newtype Module = Module [Rule] deriving (Eq, Ord, Show)

instance Expression Module where
	parser = res where
		line = do
			spaces
			option Nothing $ do
				r <- parser
				spaces
				return (Just r)
		lines = do
			r <- line
			rs <- many (newline >> line)
			return (r : rs)
		res = fmap (Module . concat . map (maybe [] (\r -> [r]))) lines
	displays (Module []) = ("" ++)
	displays (Module (rule : rules)) = displays rule .
		foldr (\rule a -> ("\n" ++) . displays rule . a) id rules