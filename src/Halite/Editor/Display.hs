module Halite.Editor.Display where

import Halite.Expression
import Halite.Editor.Draw (X, Y, Draw)
import qualified Halite.Editor.Draw as Draw
import Data.Maybe (fromMaybe)

-- | Describes the location of the user's cursor in a window, along with
-- the surronding context.
data Cursor = Cursor {

    -- | Draws the contents under the cursor with highlighting.
    highlight :: Draw,

    -- | Draws the contents under the cursor without highlighting.
    unhighlight :: Draw,

    -- | Navigates inward ("drilling" into the expression), starting
    -- from the left of the current cursor.
    navInLeft :: Cursor,

    -- | Navigates inward ("drilling" into the expression), starting
    -- from the right of the current cursor.
    navInRight :: Cursor,

    -- | Navigates outward.
    navOut :: Cursor,

    -- | Navigates left.
    navLeft :: Cursor,

    -- | Navigates right.
    navRight :: Cursor }

-- | The context needed to display an expression.
data Context a = Context {

    -- | Gets the name of the given variable.
    name :: a -> String,

    -- | The location of the topmost, leftmost point of the expression.
    pos :: (X, Y),

    -- | The cursor selecting the expression that encloses this one.
    ctxOut :: Maybe Cursor,

    -- | The cursor selecting the expression to the immediate left of this one.
    ctxLeft :: Maybe Cursor,

    -- | The cursor selecting the expression to the immediate right of this one.
    ctxRight :: Maybe Cursor }

-- | The appearance for highlighted text.
highlightAppr :: Draw.Appearance
highlightAppr = (Draw.lightBlue, Draw.white)

-- | The background for most text.
normalBack :: Draw.Color
normalBack = Draw.black

-- | The foreground color for normal text.
textFore :: Draw.Color
textFore = Draw.lightGray

-- | The foreground color for an operator.
operatorFore :: Draw.Color
operatorFore = Draw.white

-- | Displays a selectable string.
displayString :: Draw.Color -> String -> Context a -> Cursor
displayString fore str ctx = cursor 0 where
    cursor depth = Cursor {
        highlight = Draw.string highlightAppr (pos ctx) str,
        unhighlight = Draw.string (normalBack, fore) (pos ctx) str,
        navInLeft = cursor (depth + 1),
        navInRight = cursor (depth + 1),
        navOut = fromMaybe (cursor depth) (ctxOut ctx),
        navLeft = maybe (cursor depth)
            ((!! depth) . iterate navInRight) (ctxLeft ctx),
        navRight = maybe (cursor depth)
            ((!! depth) . iterate navInLeft) (ctxRight ctx) }

-- | Displays an expression using the given context.
display :: Expression a -> Context a -> Cursor
display (Exp (Var x)) ctx = displayString textFore (name ctx x) ctx
display (Exp Hole) ctx = displayString operatorFore "_" ctx
