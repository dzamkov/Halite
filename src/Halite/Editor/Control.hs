{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
module Halite.Editor.Control where

import Halite.Editor.Draw (Draw)
import qualified Halite.Editor.Draw as Draw
import Halite.Editor.Display (Shape, Highlight, Display)
import qualified Halite.Editor.Display as Display
import Data.Monoid
import Control.Applicative

-- | A filled 'Display' that represents some object. @a@ is the type of
-- an immediate child of the object and @e@ is the type of a modification
-- to the object.
data Control p e a = Monoid e => Control {

    -- | Gets information about the object associated with a 'Control'. This
    -- may include functions which modify the object by producing an @e@.
    info :: p e a,

    -- | Gets the display for a 'Control'.
    display :: Display a,

    -- | Gets a 'Control' for a child of this 'Control'. Note that the
    -- child object may have a different type than the parent object, but
    -- modifications made to the child can be mapped to the parent.
    child :: forall r. a -> (forall h b.
        Control p h b -> (h -> e) -> r) -> r }

-- | Computes the 'Shape' and 'Draw' needed to draw an unmodified control.
shapeDraw :: Control p e a -> (Shape, Highlight -> Draw)
shapeDraw control = (Display.shape layout, draw) where
    childDraw x = child control x (\c _ -> shapeDraw c)
    childShape = fst . childDraw
    layout = Display.layout (display control) childShape
    drawChild highlight x =
        let offset = Display.offset layout x
            draw = snd (childDraw x) highlight
        in Draw.translate offset draw
    draw highlight = Display.drawAround layout highlight <>
        mconcat (drawChild highlight <$> Display.holes (display control))

-- | Computes the 'Shape' of an unmodified control.
shape :: Control p e a -> Shape
shape = fst . shapeDraw

-- | Draws an unmodified control.
draw :: Control p e a -> Highlight -> Draw
draw = snd . shapeDraw

-- | A 'Control' of some modification and child type.
data AnyControl p = forall e a. AnyControl (Control p e a)
