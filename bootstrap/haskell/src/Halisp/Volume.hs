module Halisp.Volume (
	Volume,
	empty,
	null,
	single,
	union,
	difference,
	intersection,
	contains,
	intersects,
	sum,
	product,
	cut,
	refine,
	optimize
) where

import Prelude hiding (null, sum, product)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List

-- An variant of a set which allows many inclusion and binary operators, but has no
-- explicit notion of membership.
newtype Volume = Volume (Set Integer) deriving (Show, Ord, Eq)

-- The empty volume.
empty :: Volume
empty = Volume Set.empty

-- Determines whether a volume is empty.
null :: Volume -> Bool
null (Volume s) = Set.null s

-- A non-empty volume with no special properties.
single :: Volume
single = Volume (Set.singleton 0)

-- Constructs the union of two volumes.
union :: Volume -> Volume -> Volume
union (Volume xS) (Volume yS) = Volume (Set.union xS yS)

-- Constructs the difference of two volumes.
difference :: Volume -> Volume -> Volume
difference (Volume xS) (Volume yS) = Volume (Set.difference xS yS)

-- Constructs the intersection of two volumes.
intersection :: Volume -> Volume -> Volume
intersection (Volume xS) (Volume yS) = Volume (Set.intersection xS yS)

-- Determines whether the first volume is fully contained by the second.
contains :: Volume -> Volume -> Bool
contains (Volume xS) (Volume yS) = Set.isSubsetOf xS yS

-- Determines whether the given volumes intersect.
intersects :: Volume -> Volume -> Bool
intersects (Volume xS) (Volume yS) = not $ Set.null (Set.intersection xS yS)

-- Constructs the sum of two volumes, and a pair of functions which take a sub-volume
-- from each respective source volume and project it to a sub-volume of the final volume.
sum :: Volume -> Volume -> (Volume, Volume -> Volume, Volume -> Volume)
sum (Volume xS) (Volume yS) = res where
	yOffset = case Set.maxView xS of
		Just (i, _) -> i + 1
		Nothing -> 0
	final = Volume (Set.union xS $ Set.mapMonotonic (yOffset +) yS)
	leftProj volume = volume
	rightProj (Volume yS) = Volume (Set.mapMonotonic (yOffset +) yS)
	res = (final, leftProj, rightProj)

-- Constructs the product of two volumes, returning a function which takes a pair of 
-- sub-volumes from each respective source volume and projects it to a sub-volume in the 
-- final volume.
product :: Volume -> Volume -> (Volume, Volume -> Volume -> Volume)
product x@(Volume xS) y@(Volume yS) = res where
	xSize = case Set.maxView xS of
		Just (i, _) -> i + 1
		Nothing -> 0
	proj (Volume xS) (Volume yS) = Volume (Set.fromDistinctAscList [i + j * xSize |
		j <- Set.toAscList yS, i <- Set.toAscList xS])
	res = (proj x y, proj)

-- Constructs a subtraction volume. This removes a sub-volume of the given volume. The
-- final volume is returned, along with a function to project sub-volumes from the
-- original volume to the final volume.
cut :: Volume -> Volume -> (Volume, Volume -> Volume)
cut volume sub = res where
	nVolume = difference volume sub
	passProj v = difference v sub
	res = (nVolume, passProj)
	
-- Constructs a refinement of the given volume. This replaces a sub-volume of the volume
-- with a product between that sub-volume and the third volume. Two functions are
-- returned; one which projects a volume from the product sub-volume to a final volume,
-- and one which projects sub-volumes of the source volume to the final volume.
refine :: Volume -> Volume -> Volume -> (Volume, Volume -> Volume, Volume -> Volume)
refine volume sub other = res where
	diff = difference volume sub
	(prod, prodProj) = product sub other
	(nVolume, leftProj, rightProj) = sum prod diff
	innerProj v = leftProj $ prodProj sub v
	passProj v = res where
		inSub = intersection v sub
		outSub = difference v sub
		res = union (leftProj $ prodProj inSub other) (rightProj $ outSub)
	res = (nVolume, innerProj, passProj)

-- Transforms a volume in order to improve its performance given a list of the sub-volumes
-- which must be preserved. The new volume, along with a projection of sub-volumes to
-- the final volume, are returned.
optimize :: Volume -> [Volume] -> (Volume, Volume -> Volume)
optimize (Volume s) _ | Set.null s = (empty, id)
optimize (Volume s) subs = res where
	map' = Map.fromDistinctAscList $ List.map (\i -> (i, 0)) $ Set.toAscList s
	update (map, next) (Volume sub) = res where
		(nMap, vMap, n) = Set.foldr (\i (m, v, n) -> case Map.lookup ((Map.!) m i) v of
			Nothing -> (Map.insert i n m, Map.insert ((Map.!) m i) n v, n + 1)
			Just nI -> (Map.insert i nI m, v, n)) (map, Map.empty, next) sub
		res = (nMap, n)
	(map, n) = List.foldl update (map', 1) subs
	nVolume = Volume (Set.map ((Map.!) map) s)
	proj (Volume s) = Volume (Set.map ((Map.!) map) s)
	res = (nVolume, proj)