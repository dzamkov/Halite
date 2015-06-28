{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ImplicitParams #-}
module Halite.Editor.Display where

import Void
import Halite.Editor.Draw (Width, Height, X, Y, Draw)
import qualified Halite.Editor.Draw as Draw

-- | Describes a position-invariant area in which text content can (or has)
-- fit into.
data Shape

    -- | A shape that occupies a horizontal section of a single line.
    = Inline Width

    -- | A shape that occupies a block-shaped region of at least two lines.
    -- The first line may be indented by a given amount while the last line
    -- may end short (at the given offset).
    | Block Width Height X X
    deriving (Eq, Ord, Show)

-- | Indicates whether a 'Draw' should be highlighted.
type Highlight = Bool

-- | A visual object bounded by a shape.
data Display = Display {

    -- | The shape of the display.
    shape :: Shape,

    -- | Draws the contents of the display, in shape-relative coordinates.
    draw :: Highlight -> Draw }

-- | A constructor for a 'Display' that requires several holes indexed by
-- type @a@ to be filled.
data Compound a = Compound {

    -- | Gets the bounding shape for the given hole.
    bounds :: a -> Shape,

    -- | Creates a 'Display' for this compound by filling all of its holes.
    -- The offsets of each hole in the final 'Display' are also returned.
    display :: (a -> Display) -> (a -> (X, Y), Display) }

-- | Converts a display into a compound with no holes.
toCompound :: Display -> Compound Void
toCompound display = Compound {
    bounds = undefined,
    display = const (undefined, display) }

-- | Describes a global visual style for the editor.
data Style = Style {

    -- | The appearance of highlighted text.
    highlightAppr :: Draw.Appearance,

    -- | The background for most text.
    normalBack :: Draw.Color,

    -- | The foreground for an atomic symbol.
    atomFore :: Draw.Color,

    -- | The foreground color for an operator.
    operatorFore :: Draw.Color }

-- | A good default 'Style'.
defaultStyle :: Style
defaultStyle = Style {
    highlightAppr = (Draw.lightBlue, Draw.white),
    normalBack = Draw.black,
    atomFore = Draw.lightGray,
    operatorFore = Draw.white }

-- | Constructs a 'Display' for an atomic symbol.
atom :: (?style :: Style) => String -> Display
atom str = Display {
    shape = Inline (length str),
    draw = \highlight ->
        let appr True = highlightAppr ?style
            appr False = (normalBack ?style, atomFore ?style)
        in Draw.string (appr highlight) (0, 0) str }
