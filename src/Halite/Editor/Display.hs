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

-- | Describes the graphical contents of a position-invariant area with
-- unfilled /holes/ of type @a@.
data Layout a = Layout {

    -- | The shape of the layout area, including holes.
    shape :: Shape,

    -- | The offset of the given hole in layout coordinates.
    offset :: a -> (X, Y),

    -- | Draws the contents of the layout, excluding holes.
    drawAround :: Highlight -> Draw }

-- | Describes a figure with an ordered collection of /holes/ of type @a@.
-- The shape and contents of the holes can be given to produce a 'Draw'.
data Display a = Eq a => Display {

    -- | Gets the hole directly before the given hole.
    before :: Maybe a -> Maybe a,

    -- | Gets the hole directly after the given hole.
    after :: Maybe a -> Maybe a,

    -- | Gets the bounding shape that the contents of the given hole must fit
    -- in.
    limits :: a -> Shape,

    -- | Constructs a layout for this 'Display' by assigning a shape to
    -- all holes.
    layout :: (a -> Shape) -> Layout a }

-- | Gets an ordered list of all holes in a display.
holes :: Display a -> [a]
holes display = go (after display Nothing) where
    go Nothing = []
    go cur@(Just head) = head : go (after display cur)

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

-- | Constructs a 'Display' with no holes.
concrete :: Shape -> (Highlight -> Draw) -> Display Void
concrete shape draw = Display {
    before = const Nothing,
    after = const Nothing,
    limits = undefined,
    layout = const Layout {
        shape = shape,
        offset = undefined,
        drawAround = draw }}

-- | Constructs a 'Display' for an atomic symbol.
atom :: (?style :: Style) => String -> Display Void
atom str = concrete (Inline (length str)) $ \highlight ->
    let appr True = highlightAppr ?style
        appr False = (normalBack ?style, atomFore ?style)
    in Draw.string (appr highlight) (0, 0) str
