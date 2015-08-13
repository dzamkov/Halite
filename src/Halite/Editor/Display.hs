{-# LANGUAGE ImplicitParams #-}
module Halite.Editor.Display (
    module Halite.Editor.Display.Base,
    atom,
    operator,
    spaceList,
    bracketr
) where

import Halite.Editor.Display.Base
import Halite.Editor.Style
import Data.Monoid

-- | Constructs a 'Display' for an atom with the given name.
atom :: (?style :: Style) => String -> Display a
atom = text (atomFore ?style)

-- | Constructs a 'Display' for an operator containing the given text.
operator :: (?style :: Style) => String -> Display a
operator = text (operatorFore ?style)

-- | Constructs a 'Display' consisting of the given 'Display's seperated by
-- whitespace.
spaceList :: [Display a] -> Display a
spaceList items = choice
    (foldr1 (\x y -> x <> space 1 <> y) $ map inline items) -- prefer inline
    (foldr1 (\x y -> x <> spaceBreak <> y) items)

-- | Surronds a 'Display' with rounded brackets (parentheses).
bracketr :: (?style :: Style) => Display a -> Display a
bracketr x = operator "(" <> indent (minorIndent ?style) x <> operator ")"
