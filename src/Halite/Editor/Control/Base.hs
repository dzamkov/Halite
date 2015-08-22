{-# LANGUAGE RankNTypes #-}
module Halite.Editor.Control.Base where

import Halite.Editor.Draw (X, Y)
import Halite.Editor.Display.Base (Display)
import qualified Halite.Editor.Display.Base as Display
import Control.Monad.State
import Control.Monad.Identity
import Control.Applicative

-- | A marker for 'Display's created for 'Control's. These markers are used
-- to delimit sections.
data Marker = Begin | End

-- | Identifies a section within a 'Control'.
type Section = [Int]

-- | Isomorphic to @'Section' -> a@. Used for performance reasons.
data SectionF a = SectionF a (Int -> SectionF a)

data Command

-- | An editable visual representation of an object of type @o@ in an
-- environment of type @i@.
data Control i o = forall s. Control {

    -- | The initial 'Display' for a 'Control'. Note that although the entire
    -- 'Control' is technically a section, the 'Begin' and 'End' markers for
    -- it are implied and do not need to appear in the 'Display'.
    display :: i -> Display Marker,

    -- | The initial value of a 'Control'.
    value :: o,

    interact :: SectionF (Command -> Delta i o) }

-- | Describes a change in a 'Control'
data Delta i o = Delta {

    -- | The smallest section that encloses the changes to the control.
    section :: Section,

    displayN :: i -> Display Marker,

    valueN :: o,


    }

    

-- | A dynamic visual representation of an object of type @a@ in an
-- environment of type @e@ obtained by decomposing the object into a list of
-- children which can swapped out and substituted as needed. The type
-- @p h b@ describes a potential kind of a child with environment type
-- @h@ and object type @b@.
data Control p e a = Control {

    -- | Iterates through all children in a 'Control', obtaining their current
    -- value and 'Display', and returns the resulting value and 'Display'
    -- for the 'Control'.
    traverse :: forall f r. (Applicative f)
        => (forall h b. p h b -> b -> f (b, h -> Display r))
        -> f (a, e -> Display r) }

-- | Determines how many children a 'Control' has.
childCount :: Control p e a -> Int
childCount control =
    let f = traverse control (\_ _ -> modify (+ 1) >> return undefined)
        (_, c) = runState f 0
    in c

-- | Gets the initial value for a 'Control'.
initial :: Control p e a -> a
initial control = fst $ runIdentity $ traverse control
    (\_ b -> Identity (b, undefined))

-- | Displays an unmodified 'Control'.
display :: (forall h b. p h b -> h -> b -> Display r)
    -> Control p e a -> e -> Display r
display displayChild control =
    let f p b = Identity (b, \h -> displayChild p h b)
    in snd $ runIdentity $ traverse control f
