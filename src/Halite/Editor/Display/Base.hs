module Halite.Editor.Display.Base (
    Appearance,
    Instance (..),
    translate,
    Display,
    nil,
    zero,
    marker,
    space,
    varSpace,
    text,
    break,
    spaceBreak,
    choice,
    append,
    indent,
    inline,
    Shape (..),
    Fit (..),
    instantiate
) where

import Prelude hiding (map, break)
import Halite.Editor.Draw (Width, Height, X, Y, Draw)
import qualified Halite.Editor.Draw as Draw
import qualified Data.List as List
import Data.Maybe (fromMaybe)
import Data.Monoid
import Control.Applicative

-- | The background color, and optional overrided foreground color, that
-- a 'Display' can be drawn with.
type Appearance = (Draw.Color, Maybe Draw.Color)

-- | Contains the information needed to draw a hole-less 'Display' that has
-- been fitted to a known shape, and records the locations of the markers in
-- the 'Display'.
data Instance a = Instance {

    -- | The ordered list of markers that appear in the 'Instance', along
    -- with their relative offsets.
    markers :: [(a, (X, Y))],

    -- | Draws the contents of an 'Instance', in shape-relative coordinates.
    draw :: Appearance -> Draw }

instance Monoid (Instance a) where
    mempty = Instance {
        markers = [],
        draw = const mempty }
    mappend a b = Instance {
        markers = markers a ++ markers b,
        draw = (<>) <$> draw a <*> draw b }

-- | Translates an 'Instance'.
translate :: (X, Y) -> Instance a -> Instance a
translate offset@(x, y) inst = Instance {
    markers = List.map
        (\(r, (x', y')) -> (r, (x + x', y + y')))
        (markers inst),
    draw = Draw.translate offset <$> draw inst }

-- | Describes a primitive fixed-size single-line item in a 'Display'.
data Word a
    = Space Width
    | Text Draw.Color String
    | Marker a
    deriving (Eq, Ord, Show)

-- | Gets the total width of a 'Word'.
wordWidth :: Word a -> Width
wordWidth (Space w) = w
wordWidth (Text _ s) = length s
wordWidth (Marker _) = 0

-- | Creates an 'Instance' for a space.
spaceInstantiate :: Width -> (X, Y) -> Instance a
spaceInstantiate w offset = Instance {
    markers = [],
    draw = \(back, _) -> Draw.space back offset w }

-- | Creates an 'Instance' for a 'Word'.
wordInstantiate :: Word a -> (X, Y) -> Instance a
wordInstantiate (Space w) = spaceInstantiate w
wordInstantiate (Text c s) = \offset -> Instance {
    markers = [],
    draw = \(back, fore) -> Draw.string (back, fromMaybe c fore) offset s}
wordInstantiate (Marker r) = \offset -> Instance {
    markers = [(r, offset)],
    draw = const mempty }

-- | A fixed-size single-line block of 'Word's, with possible trailing
-- whitespace.
type Phrase a = [Word a]

-- | Prepends a 'Word' to a 'Phrase'.
phrasePrepend :: Word a -> Phrase a -> Phrase a
phrasePrepend (Space w) (Space w' : p) = Space (w + w') : p
phrasePrepend (Text c s) (Text c' s' : p) | c == c' = Text c (s ++ s') : p
phrasePrepend w p = w : p

-- | Gets the total width of a 'Phrase'.
phraseWidth :: Phrase a -> Width
phraseWidth = sum . List.map wordWidth

-- | Creates an 'Instance' for a 'Phrase', assumed to be on a single line with
-- no additional spacing.
phraseInstantiate :: Phrase a -> (X, Y) -> Instance a
phraseInstantiate phrase offset = fst $ List.foldl
    (\(accum, offset@(x, y)) word ->
        (accum <> wordInstantiate word offset,
        (x + wordWidth word, y)))
    (mempty, offset) phrase

-- | Describes the contents of a line within a 'Display' as the list of
-- 'Word's before the first variable space, and, if it exists, the list of
-- 'Word's after the variable space.
data Line a = Line (Phrase a) (Maybe (Phrase a))
    deriving (Eq, Ord, Show)
instance Monoid (Line a) where
    mempty = Line mempty Nothing
    mappend (Line af Nothing) (Line bf bl) = Line (af <> bf) bl
    mappend (Line af (Just al)) (Line bf Nothing) = Line af (Just $ al <> bf)
    mappend (Line af (Just al)) (Line bf (Just bl)) =
        Line af (Just $ al <> bf <> bl)

-- | Prepends a 'Word' to a 'Line'.
linePrepend :: Word a -> Line a -> Line a
linePrepend w (Line f l) = Line (phrasePrepend w f) l

-- | Creates an 'Instance' for a 'Line' fitted to an enclosing line of the
-- given width, or returns 'Nothing' if the 'Line' can't fit.
lineInstantiate :: Line a -> Width -> Maybe ((X, Y) -> Instance a)
lineInstantiate (Line x Nothing) w = if w == phraseWidth x
    then Just (phraseInstantiate x)
    else Nothing
lineInstantiate (Line f (Just l)) w =
    let fw = phraseWidth f
        lw = phraseWidth l
        vw = w - fw - lw
    in if vw >= 0
    then Just (\(x, y) ->
        phraseInstantiate f (x, y) <>
        spaceInstantiate vw (x + fw, y) <>
        phraseInstantiate l (x + fw + vw, y))
    else Nothing

-- | A non-empty list of lines. When concatenating, the last line of the
-- first block and the first line of the second block will be merged together.
data Block a = Block [Line a] (Line a)
    deriving (Eq, Ord, Show)
instance Monoid (Block a) where
    mempty = Block [] mempty
    mappend (Block ai al) (Block [] bl) = Block ai (al <> bl)
    mappend (Block ai al) (Block (bh : bt) bl) =
        Block (ai ++ (al <> bh) : bt) bl

-- | Prepends a line to the first line of a block.
blockPrepend :: Line a -> Block a -> Block a
blockPrepend l' (Block [] l) = Block [] (l' <> l)
blockPrepend l' (Block (ih : it) l) = Block ((l' <> ih) : it) l

-- | Applies an indentation to all but the first line in a block.
blockIndent :: Width -> Block a -> Block a
blockIndent _ b@(Block [] _) = b
blockIndent w (Block (h : t) l) =
    Block (h : List.map (linePrepend (Space w)) t) (linePrepend (Space w) l)

-- | Constructs a block containing the given word on its own line and
-- nothing else.
blockFromWord :: Word a -> Block a
blockFromWord word = Block [] $ Line [word] Nothing

-- | A block containing a variable-size space and nothing else.
blockVarSpace :: Block a
blockVarSpace = Block [] $ Line mempty $ Just mempty

-- | A block containing a line break and nothing else.
blockBreak :: Block a
blockBreak = Block [mempty] mempty

-- | Describes the non-primitive contents of a 'Display'.
data Cont a
    = Nil
    | Zero
    | Choice (Display a) (Display a)
    deriving (Eq, Ord, Show)

-- | Describes content to be displayed in an editor, including its indention,
-- alignment, layout and coloring information. Content may include /markers/,
-- which are zero-width elements, identified by values of type @a@, whose
-- offsets are recorded in 'Instance's of the 'Display'.
data Display a = Display (Block a) (Cont a)
    deriving (Eq, Ord, Show)
instance Monoid (Display a) where
    mempty = nil
    mappend = append

-- | A 'Display' with no content. Note that a 'nil' is zero-width and
-- can not occupy space by itself. This is the identity for 'append'.
nil :: Display a
nil = Display mempty Nil

-- | A 'Display' with no valid fittings. This is the identity for 'choice'
-- and the absorbing element of 'append'.
zero :: Display a
zero = Display mempty Zero

-- | Constructs a 'Display' for a marker with the given identifier.
marker :: a -> Display a
marker r = Display (blockFromWord $ Marker r) Nil

-- | Constructs a 'Display' for a space of the given width.
space :: Width -> Display a
space w = Display (blockFromWord $ Space w) Nil

-- | A variable-width space. This may occupy any amount of space on a single
-- line, with preference towards being shorter.
varSpace :: Display a
varSpace = Display blockVarSpace Nil

-- | Constructs a 'Display' for the given text.
text :: Draw.Color -> String -> Display a
text _ [] = nil
text c s = Display (blockFromWord $ Text c s) Nil

-- | A 'Display' that separates two lines. Note that a 'break' is zero-width
-- and can not occupy space by itself.
break :: Display a
break = Display blockBreak Nil

-- | Equivalent to @'varSpace' <> 'break'@. Can be used to end a line, even
-- when the line has not been completely filled.
spaceBreak :: Display a
spaceBreak = varSpace <> break

-- | Constructs a 'Display' that appears as one of the given 'Display's,
-- with preference to the left.
choice :: Display a -> Display a -> Display a
choice (Display _ Zero) b = b
choice a (Display _ Zero) = a
choice a b = Display mempty $ Choice a b

-- | Concatenates the contents of two 'Display's.
append :: Display a -> Display a -> Display a
append (Display _ Zero) _ = zero
append (Display ax Nil) (Display bx bc) = Display (ax <> bx) bc
append (Display ax (Choice ca cb)) b =
    Display ax (Choice (append ca b) (append cb b))

-- | Applies an indentation of the given width to a 'Display'. Note that
-- indentation must be positive and does not affect the first line of the
-- 'Display'.
indent :: Width -> Display a -> Display a
indent w (Display x c) = Display (blockIndent w x) nc where
    nc = case c of
        Nil -> Nil
        Zero -> Zero
        Choice a b -> Choice (indent w a) (indent w b)

-- | Forces a 'Display' to be inline. If no possible, the 'Display'
-- becomes 'zero'.
inline :: Display a -> Display a
inline a@(Display (Block [] _) Nil) = a
inline (Display x@(Block [] _) (Choice a b)) =
    append (Display x Nil) (choice (inline a) (inline b))
inline _ = zero

-- | Describes a position-invariant area that a 'Display' can take.
data Shape
    = Inline Width
    | Multiline Width Width Height Width
    deriving (Eq, Ord, Show)

-- | Describes a set of shapes that a 'Display' can be fitted to. Upon
-- instantiation, the 'Display' will take one of the available shapes.
data Fit
    = Fixed Shape
    | Variable Width Width
    deriving (Eq, Ord, Show)

-- | Gets the width and relative X offset of the first line of a 'Fit', and
-- returns the 'Fit' for the remaining lines, if they exist.
fitTakeLine :: Fit -> (X, Width, Maybe Fit)
fitTakeLine (Fixed (Inline w)) = (0, w, Nothing)
fitTakeLine (Fixed (Multiline wFirst w 0 wLast)) =
    (w - wFirst, wFirst, Just $ Fixed $ Inline wLast)
fitTakeLine (Fixed (Multiline wFirst w h wLast)) =
    (w - wFirst, wFirst, Just $ Fixed $ Multiline w w (h - 1) wLast)
fitTakeLine (Variable wFirst w) =
    (w - wFirst, wFirst, Just $ Variable w w)

-- | Fits a display to a shape, returning all possible fittings in order of
-- preference.
instantiate :: Display a -> Fit -> [Instance a]
instantiate (Display (Block i l) c) fit = res where
    instantiate' _ _ _ Nothing _ _ = []
    instantiate' (ih : it) l c (Just fit) y accum =
        let (x, w, fitNext) = fitTakeLine fit
        in case lineInstantiate ih w of
            Nothing -> []
            Just instIh -> instantiate' it l c fitNext (y + 1)
                (accum <> instIh (x, y))
    instantiate' [] l Nil (Just fit) y accum =
        let (x, w, fitNext) = fitTakeLine fit
        in case (fitNext, lineInstantiate l w) of
            (Just (Fixed _), _) -> []
            (_, Nothing) -> []
            (_, Just instL) -> return (accum <> instL (x, y))
    instantiate' [] _ Zero _ _ _ = []
    instantiate' [] l (Choice (Display ab ac) (Display bb bc)) fit y accum =
        let Block ai al = blockPrepend l ab
            Block bi bl = blockPrepend l bb
        in instantiate' ai al ac fit y accum ++
            instantiate' bi bl bc fit y accum
    res = instantiate' i l c (Just fit) 0 mempty
