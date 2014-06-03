module Halisp.Region (
	Region,
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

-- An variant of a set that is infinitely divisible and supports many
-- inclusion/relationship operations, but has no explicit notion of membership.
newtype Region = Region (Set Integer) deriving (Show, Ord, Eq)

-- The empty region.
empty :: Region
empty = Region Set.empty

-- Determines whether a region is empty.
null :: Region -> Bool
null (Region s) = Set.null s

-- A non-empty region with no special properties.
single :: Region
single = Region (Set.singleton 0)

-- Constructs the union of two regions.
union :: Region -> Region -> Region
union (Region xS) (Region yS) = Region (Set.union xS yS)

-- Constructs the difference of two regions.
difference :: Region -> Region -> Region
difference (Region xS) (Region yS) = Region (Set.difference xS yS)

-- Constructs the intersection of two regions.
intersection :: Region -> Region -> Region
intersection (Region xS) (Region yS) = Region (Set.intersection xS yS)

-- Determines whether the first region fully contains the second.
contains :: Region -> Region -> Bool
contains (Region xS) (Region yS) = Set.isSubsetOf yS xS

-- Determines whether the given regions intersect.
intersects :: Region -> Region -> Bool
intersects (Region xS) (Region yS) = not $ Set.null (Set.intersection xS yS)

-- Constructs the sum of two regions, and a pair of functions which take a sub-region
-- from each respective source region and project it to a sub-region of the final region.
sum :: Region -> Region -> (Region, Region -> Region, Region -> Region)
sum (Region xS) (Region yS) = res where
	yOffset = case Set.maxView xS of
		Just (i, _) -> i + 1
		Nothing -> 0
	final = Region (Set.union xS $ Set.mapMonotonic (yOffset +) yS)
	leftProj region = region
	rightProj (Region yS) = Region (Set.mapMonotonic (yOffset +) yS)
	res = (final, leftProj, rightProj)

-- Constructs the product of two regions, returning a function which takes a pair of 
-- sub-regions from each respective source region and projects it to a sub-region in the 
-- final region.
product :: Region -> Region -> (Region, Region -> Region -> Region)
product x@(Region xS) y@(Region yS) = res where
	xSize = case Set.maxView xS of
		Just (i, _) -> i + 1
		Nothing -> 0
	proj (Region xS) (Region yS) = Region (Set.fromDistinctAscList [i + j * xSize |
		j <- Set.toAscList yS, i <- Set.toAscList xS])
	res = (proj x y, proj)

-- Constructs a subtraction region. This removes a sub-region of the given region. The
-- final region is returned, along with a function to project sub-regions from the
-- original region to the final region.
cut :: Region -> Region -> (Region, Region -> Region)
cut region sub = res where
	nRegion = difference region sub
	passProj v = difference v sub
	res = (nRegion, passProj)
	
-- Constructs a refinement of the given region. This replaces a sub-region of the region
-- with a product between that sub-region and the third region. Two functions are
-- returned; one which projects a region from the product sub-region to a final region,
-- and one which projects sub-regions of the source region to the final region.
refine :: Region -> Region -> Region -> (Region, Region -> Region, Region -> Region)
refine region sub other = res where
	diff = difference region sub
	(prod, prodProj) = product sub other
	(nRegion, leftProj, rightProj) = sum prod diff
	innerProj v = leftProj $ prodProj sub v
	passProj v = res where
		inSub = intersection v sub
		outSub = difference v sub
		res = union (leftProj $ prodProj inSub other) (rightProj $ outSub)
	res = (nRegion, innerProj, passProj)

-- Transforms a region in order to improve its performance given a list of the sub-regions
-- which must be preserved. The new region, along with a projection of sub-regions to
-- the final region, are returned.
optimize :: Region -> [Region] -> (Region, Region -> Region)
optimize (Region s) _ | Set.null s = (empty, id)
optimize (Region s) subs = res where
	map' = Map.fromDistinctAscList $ List.map (\i -> (i, 0)) $ Set.toAscList s
	update (map, next) (Region sub) = res where
		(nMap, vMap, n) = Set.foldr (\i (m, v, n) -> case Map.lookup ((Map.!) m i) v of
			Nothing -> (Map.insert i n m, Map.insert ((Map.!) m i) n v, n + 1)
			Just nI -> (Map.insert i nI m, v, n)) (map, Map.empty, next) sub
		res = (nMap, n)
	(map, n) = List.foldl update (map', 1) subs
	nRegion = Region (Set.map ((Map.!) map) s)
	proj (Region s) = Region (Set.map ((Map.!) map) s)
	res = (nRegion, proj)