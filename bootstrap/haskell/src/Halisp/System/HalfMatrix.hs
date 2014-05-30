module Halisp.System.HalfMatrix (
	HalfMatrix (..),
	empty,
	singleton,
	replicate,
	generate,
	(!),
	accum,
	map,
	imap,
	fold,
	ifold,
	symm
) where

import Prelude hiding (replicate, (!), map)
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import qualified Data.List as List

-- A square matrix of values of the given type, analogous to a vector. The matrix only
-- stores values for indices where the first component is less than, or equal to, the
-- second component.
data HalfMatrix a = HalfMatrix {
	size :: Int, 
	source :: Vector a }

-- Empty half-matrix
empty :: HalfMatrix a
empty = HalfMatrix { size = 0, source = Vector.empty }

-- Matrix with exactly one element
singleton :: a -> HalfMatrix a
singleton value = HalfMatrix { size = 1, source = Vector.singleton value }

-- Constructs a half-matrix with the given size that has the given value in each position.
replicate :: Int -> a -> HalfMatrix a
replicate size value = generate size (const value)

-- Generates a half-matrix of the given length by applying the given function to each
-- index.
generate :: Int -> ((Int, Int) -> a) -> HalfMatrix a
generate size f = res where
	fInner i = res where
		x = i `mod` size
		y = i `div` size
		res = if x <= y then f (x, y) else undefined
	res = HalfMatrix { size = size, source = Vector.generate (size * size) fInner }

-- Indexing
(!) :: HalfMatrix a -> (Int, Int) -> a
(!) matrix (x, y) = (Vector.!) (source matrix) (x + y * size matrix)

-- Analogous to 'Vector.accum'
accum :: (a -> b -> a) -> HalfMatrix a -> [((Int, Int), b)] -> HalfMatrix a
accum f matrix items = matrix { source = Vector.accum f (source matrix) $
	List.map (\((x, y), e) -> (x + y * size matrix, e)) items }

-- Maps a function over a half-matrix
map :: (a -> b) -> HalfMatrix a -> HalfMatrix b
map f = imap (const f)

-- Applies a function to every index/value pair
imap :: ((Int, Int) -> a -> b) -> HalfMatrix a -> HalfMatrix b
imap f matrix = res where
	fInner i e = res where
		x = i `mod` size matrix
		y = i `div` size matrix
		res = if x <= y then f (x, y) e else undefined
	res = matrix { source = Vector.imap fInner $ source matrix }

-- Fold over a matrix.
fold :: (a -> b -> a) -> a -> HalfMatrix b -> a
fold f = ifold (\accum _ e -> f accum e)

-- Fold with indices over a half-matrix
ifold :: (a -> (Int, Int) -> b -> a) -> a -> HalfMatrix b -> a
ifold f accum matrix = res where
	fInner accum i e = res where
		x = i `mod` size matrix
		y = i `div` size matrix
		res = if x <= y then f accum (x, y) e else accum
	res = Vector.ifoldl fInner accum $ source matrix

-- Interpreting a half-matrix as a symmetric matrix, gets the element at the given index.
-- A different mapping is applied based on which section of the matrix the element occurs
-- at.
symm :: (a -> b) -> (a -> b) -> (a -> b) -> HalfMatrix a -> (Int, Int) -> b
symm fLower fDia fUpper matrix (i, j) = case compare i j of
	LT -> fLower $ matrix ! (i, j)
	EQ -> fDia $ matrix ! (i, i)
	GT -> fUpper $ matrix ! (j, i)