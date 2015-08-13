{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RankNTypes #-}
module Halite.Editor.Control where

import Halite.Editor.Draw (X, Y)
import Halite.Editor.Display (Display)
import qualified Halite.Editor.Display as Display

-- | An interactive visual representation of an object where @e@ is the type of
-- a possible modification to the object.
data Control p e = forall s a. Control {

    -- | The initial state for the 'Control'.
    initial :: s,

    -- | Updates the state of the 'Control' in response to the given
    -- modification, returning the new state and a 'Bool' indicating whether
    -- the 'Control' needs to be redisplayed. The modification may cause the
    -- underlying object to be undisplayable by the 'Control'; in which case,
    -- 'Nothing' is returned.
    update :: e -> s -> Maybe (s, Bool),

    -- | Identifies the children for this 'Control' and their order of
    -- appearance when using 'display'.
    children :: [a],

    -- | Describes a child of this 'Control'.
    child :: a -> Child p e,

    -- | Gets a 'Display' for this 'Control' when provided 'Display's
    -- for its children.
    display :: forall r. s -> (a -> Display r) -> Display r }

-- | Describes a child element of a 'Control'.
data Child p e = forall h. Child {

    -- | Describes the contents of the 'Child' before any modifications
    -- have occured.
    info :: p h,

    -- | Describes the relationship between the parent object and the
    -- child object.
    relation :: Relation e h }

-- | Describes a composition relationship between two objects where the parent
-- object has modification type @e@ and the child object has modification
-- type @h@.
data Relation e h = Relation {

    -- | Maps a modification of the child to a modification of the parent.
    raiseMod :: h -> e,

    -- | Maps a modification of the parent to a modification of the child,
    -- or returns 'Nothing' if no modification to the child is being made.
    lowerMod :: e -> Maybe h }

-- | Displays an unmodified 'Control'.
displayDefault :: (forall h. p h -> Display r) -> Control p e -> Display r
displayDefault d Control { .. } =
    display initial ((\Child { info } -> d info) . child)
