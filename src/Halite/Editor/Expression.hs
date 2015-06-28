{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE GADTs #-}
module Halite.Editor.Expression where

import Void
import Halite.Expression
import Halite.Editor.Display (Shape, Style)
import qualified Halite.Editor.Display as Display
import Halite.Editor.Control (Control (Control), AnyControl (AnyControl))
import qualified Halite.Editor.Control as Control

-- | A concrete human-readable symbol that may be used to identify a value.
data Symbol
    = Atom String

-- | A procedure which accesses an expression context.
type ContextM v a = (v -> Symbol) -> a

-- | Gets the symbol assigned to the given variable.
getVarSymbol :: v -> ContextM v Symbol
getVarSymbol var lookup = lookup var

-- | The information type for a 'Control' consisting of 'Expression's.
data Info s e a where
    InfoExp :: Expression v -> Info s Void a

-- | Builds a control for the given expression.
build :: (?style :: Style) => Expression a
    -> Shape -> ContextM a (AnyControl Info)
build exp@(Exp (Var x)) _ = do
    Atom str <- getVarSymbol x
    return $ AnyControl Control {
        Control.info = InfoExp exp,
        Control.initial = (),
        Control.update = undefined,
        Control.compound = \_ _ -> Display.toCompound $ Display.atom str,
        Control.child = undefined }
build _ _ = error "not implemented" -- TODO
