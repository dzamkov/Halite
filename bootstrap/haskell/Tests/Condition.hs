{-# LANGUAGE MultiParamTypeClasses #-}
module Tests.Condition where
import Test.HUnit
import Halisp.Condition (Condition, (==^), (&&^), (||^))
import qualified Halisp.Condition as Condition
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List

data Term a = Var a | Val Integer deriving (Eq, Ord, Show)
instance Condition.Formula Term where
	frefers m (Var x) = m x
	frefers _ (Val x) = False
	fmap m (Var x) = Var (m x)
	fmap _ (Val x) = Val x
instance Condition.Term () Term where
	tvar () x = Var x
	tsub () m (Var x) = m x
	tsub () _ (Val x) = Val x

data Cons a = Less (Term a) (Term a) deriving (Eq, Ord, Show)
instance Condition.Formula Cons where
	frefers m (Less x y) = Condition.frefers m x || Condition.frefers m y
	fmap m (Less x y) = Less (Condition.fmap m x) (Condition.fmap m y)
instance Condition.Constraint () Cons Term where
	csub () m (Less x y) = case (Condition.tsub () m x, Condition.tsub () m y) of
		(Val x, Val y) -> Condition.fromBool (x < y)
		(x, y) -> Condition.simple $ Less x y
	ceq () (Val x) (Val y) = Condition.fromBool (x == y)
	ceq () (Var x) (Var y) | x == y = Condition.always
	ceq () (Var x) y = Condition.solutionFromList [(x, y)]
	ceq () x (Var y) = Condition.solutionFromList [(y, x)]

equal = Condition.ceq ()
less x y = Condition.simple (Less x y)
notEqual x y = (less x y ||^ less y x)
oneOf x ys = Condition.disjunction $ List.map (\y -> x ==^ y) ys
between x y z = Condition.simples [Less x y, Less y z]

resolve (Less x y) = case y of
	(Val ys) -> oneOf x [Val y | y <- [0 .. ys - 1]]
	y -> Condition.simple $ Less x y

assertConsistent cond = assertBool ("inconsistent condition: " ++ show cond) $
	Condition.consistent cond

assertSolutions expected cond = do
	let (solutions, nCond) = Condition.extract cond
	assertBool "not fully solved" (Condition.isNever nCond)
	assertEqual "for solutions, "
		(Set.fromList $ List.map (Map.map (Condition.fmap Left) . Map.fromList) expected)
		(Set.fromList $ List.sort solutions)
		
solution = do
	let sol = [("a", Val 145), ("b", Val 200)]
	let cond = Condition.solutionFromList sol
	assertConsistent (cond :: Condition Cons Term String)
	assertSolutions [sol] cond
	assertBool "isSolvable incorrect" (Condition.isSolvable cond)

square n = do
	let values = [Val x | x <- [0 .. n - 1]]
	let cond = Condition.conjunction () $
		[oneOf (Var "a") values,
		oneOf (Var "b") values]
	assertConsistent (cond :: Condition Cons Term String)
	let sols = [[("a", Val x), ("b", Val y)] | x <- [0 .. n - 1], y <- [0 .. n - 1]]
	assertSolutions sols cond
	
substitution = do
	let cond = less (Var (Left ())) (Var (Right ()))
	assertConsistent (cond :: Condition Cons Term (Either () ()))
	assertBool "expected contingent" $
		(not (Condition.isAlways cond) || not (Condition.isNever cond))
	let cond1 = Condition.sub () (either (const $ Val 3) (const $ Val 10)) cond
	assertConsistent (cond1 :: Condition Cons Term ())
	assertBool "expected 3 < 10 to be always" $ Condition.isAlways cond1
	let cond2 = Condition.sub () (either (const $ Val 30) (const $ Val 13)) cond
	assertConsistent (cond2 :: Condition Cons Term ())
	assertBool "expected 30 < 13 to be never" $ Condition.isNever cond2

composition1 = do
	let cond = Condition.conjunction () $
		[oneOf (Var "a") [Val 0, Val 5],
		less (Var "a") (Val 3)]
	assertConsistent cond
	assertSolutions [[("a", Val 0)]] cond
	
composition2 = do
	let cond = Condition.conjunction () $
		[oneOf (Var "a") [Val 1, Val 2, Val 3],
		notEqual (Var "a") (Val 2)]
	assertConsistent cond
	assertSolutions [[("a", Val 1)], [("a", Val 3)]] cond
		
permutations2 = do
	let cond = Condition.conjunction () $
		[oneOf (Var "a") [Val 0, Val 1],
		oneOf (Var "b") [Val 0, Val 1],
		notEqual (Var "a") (Var "b")]
	assertConsistent cond
	let sols = [[("a", Val 0), ("b", Val 1)], [("a", Val 1), ("b", Val 0)]]
	assertSolutions sols cond

permutations3 = do
	let cond = Condition.conjunction () $
		[oneOf (Var "a") [Val 0, Val 1, Val 2],
		oneOf (Var "b") [Val 0, Val 1, Val 2],
		oneOf (Var "c") [Val 0, Val 1, Val 2],
		notEqual (Var "a") (Var "b"),
		notEqual (Var "b") (Var "c"),
		notEqual (Var "c") (Var "a")]
	assertConsistent cond
	let sols = [
		[("a", Val 0), ("b", Val 1), ("c", Val 2)], 
		[("a", Val 0), ("b", Val 2), ("c", Val 1)],
		[("a", Val 2), ("b", Val 0), ("c", Val 1)], 
		[("a", Val 1), ("b", Val 0), ("c", Val 2)],
		[("a", Val 1), ("b", Val 2), ("c", Val 0)], 
		[("a", Val 2), ("b", Val 1), ("c", Val 0)]]
	assertSolutions sols cond
	
exists = do
	let cond = Condition.existsFromList ["x"] $ Condition.conjunction () $
		[oneOf (Var "x") [Val 0, Val 1, Val 2],
		less (Var "x") (Val 1)]
	assertBool "expected always" $ Condition.isAlways cond
	
bind = do
	let cond' = Condition.conjunction () $
		[less (Var "y") (Val 5),
		less (Var "x") (Var "y")]
	assertConsistent cond'
	let cond = Condition.bind () resolve $ Condition.bind () resolve cond'
	assertConsistent cond
	let sols = [[("x", Val x), ("y", Val y)] | y <- [0 .. 4], x <- [0 .. y - 1]]
	assertSolutions sols cond
	
indirect = do
	let cond = Condition.existsFromList ["c"] $ Condition.conjunction () $
		[oneOf (Var "a") [Val 0, Val 1],
		equal (Var "d") (Var "c"),
		equal (Var "e") (Var "b"),
		equal (Var "c") (Var "e"),
		equal (Var "a") (Var "d")]
	assertConsistent (cond :: Condition Cons Term String)
	let sols = [[("a", Val x), ("b", Val x), ("d", Val x), ("e", Val x)]
		| x <- [0, 1]]
	assertSolutions sols cond

challenge = do
	let apart x y = Condition.existsRightInt 1 $ between
		(Condition.fmap Left x) (Var $ Right 0) (Condition.fmap Left y)
	let cond = Condition.bind () resolve $  Condition.bind () resolve $ 
		(Condition.existsFromList ["c"] $ Condition.conjunction ()
		[between (Val 4) (Var "a") (Val 9),
		equal (Var "b") (Var "c"),
		between (Val 6) (Var "c") (Val 14),
		apart (Var "a") (Var "b"),
		notEqual (Var "c") (Val 12)]) ||^ between (Var "b") (Var "a") (Val 13)
	assertConsistent cond
	let sols = [[("a", Val a), ("b", Val b)] | (a, b) <-
		[(a, b) | a <- [5 .. 8], b <- [7 .. 13], a + 1 < b, b /= 12] ++
		[(a, b) | a <- [0 .. 12], b <- [0 .. a - 1]]]
	assertSolutions sols cond
	

tests = test [
	"solution" ~: solution,
	"square2" ~: square 2,
	"square5" ~: square 5,
	"substitution" ~: substitution,
	"composition1" ~: composition1,
	"composition2" ~: composition2,
	"permutations2" ~: permutations2,
	"permutations3" ~: permutations3,
	"exists" ~: exists,
	"bind" ~: bind,
	"indirect" ~: indirect,
	"challenge" ~: challenge ]