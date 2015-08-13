module Halite.Editor.Style where

import Halite.Editor.Draw (Width, Color)
import qualified Halite.Editor.Draw as Draw

-- | Describes the customizable visual properties of an editor.
data Style = Style {
    normalBack :: Color,
    highlightBack :: Color,
    highlightFore :: Color,
    atomFore :: Color,
    operatorFore :: Color,
    minorIndent :: Width,
    majorIndent :: Width }

-- | The default style.
styleDefault :: Style
styleDefault = Style {
    normalBack = Draw.black,
    highlightBack = Draw.lightBlue,
    highlightFore = Draw.white,
    atomFore = Draw.lightGray,
    operatorFore = Draw.white,
    minorIndent = 2,
    majorIndent = 4 }
