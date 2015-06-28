{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
module Halite.Editor.Control where

import Halite.Editor.Compound (Shape, Display, Compound)
import qualified Halite.Editor.Compound as Compound

-- | A visual representation of an object. @s@ is the set of possible
-- variants of the object that may be displayed in the same way. @e@ is
-- a possible modification to the object.
data Control p s e a = Control {

    -- | Gets information about the object associated with a 'Control'.
    -- This may include functions which modify the object producing an @e@.
    info :: p s e a,

    -- | The initial state for the 'Control'. This is the state that the
    -- 'Control' is most suited to display.
    initial :: s,

    -- | Updates the state of the 'Control' in response to the given
    -- modification. In some cases, the modification may cause the
    -- underlying object to be undisplayable by the 'Control'.
    update :: e -> s -> Maybe s,

    -- | Gets a 'Compound' to display this 'Control'. The resulting compound
    -- is bounded by the given shape.
    compound :: s -> Shape -> Compound a,

    -- | Gets a 'Control' for a child of this 'Control'. Note that the
    -- child object may have a different type than the parent object, but
    -- modifications made to the child can be mapped to the parent.
    child :: s -> a -> Child p e }

-- | Describes a child control of a 'Control'.
data Child p e = forall s h a. Child {

    -- | The control associated with this child.
    control :: Control p s h a,

    -- | Maps a modification of the child to a modification of the parent.
    liftMod :: h -> e,

    -- | Indicates whether the scope of the given modification is limited
    -- to the child control. This implies that, while handling the
    -- modification, only the child will need to be redisplayed. Note that
    -- even if this is 'True', the modification will still alter the parent's
    -- state (as this is required for the modification to be persistant).
    isLocal :: h -> Bool }

-- | Constructs a display for a control in its initial state, given a
-- bounding shape.
display :: Control p s e a -> Shape -> Display
display control shape =
    let initial' = initial control
        compound' = compound control initial' shape
    in snd $ Compound.display compound' (\index ->
        let bound = Compound.bounds compound' index
        in (\Child { control = childControl } ->
            display childControl bound) $ child control initial' index)

-- | A control with any internal state, modification and child type.
data AnyControl p = forall s e a. AnyControl (Control p s e a)
