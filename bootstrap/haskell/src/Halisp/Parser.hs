module Halisp.Parser (
	term,
	rule,
	parse
) where

import Halisp.Term (Term (..), var, app)
import Data.Char
import Text.ParserCombinators.Parsec hiding (parse)
import qualified Text.ParserCombinators.Parsec as P

-- A parser for a term with string symbols and variables.
term :: CharParser () (Term String String)
term = do
	symOrVar <- many1 letter
	if isLower (head symOrVar) then return (var symOrVar) else do
		option (app symOrVar []) $ between (char '[') (char ']') $ do
			args <- sepBy term (spaces >> char ',' >> spaces)
			return (app symOrVar args)
			
-- A parser for a rule.
rule :: CharParser () (Term String String, Term String String)
rule = do
	left <- term
	spaces
	char '='
	spaces
	right <- term
	return (left, right)
	
-- A parser for a set of rules.
rules :: CharParser () [(Term String String, Term String String)]
rules = do
	let line = do
		spaces
		option Nothing $ do
			r <- rule
			spaces
			return (Just r)
	r <- line
	rs <- many (newline >> line)
	return ((r : rs) >>= (\l -> case l of
		Just rule -> [rule]
		Nothing -> []))
			
-- Applies a parser to a string with the assumption that there will be no parse error.
parse :: CharParser () a -> String -> a
parse parser input = case P.parse parser "" input of
	Left err -> error $ "parse failed: " ++ show err
	Right value -> value