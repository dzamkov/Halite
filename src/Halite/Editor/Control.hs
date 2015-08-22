{-# LANGUAGE GADTs #-}
module Halite.Editor.Control (
    module Halite.Editor.Control.Base
) where

import Halite.Editor.Control.Base
import Halite.Expression

-- | Assigns variables of type @a@ to 'Symbol's.
type Scope a = a -> Symbol

-- | Identifies a type that may be used for a child produced by
-- 'fromExpression'.
data EType e a where
    Exp :: EType (Scope a) (Exp a)

-- | Constructs a 'Control' for an 'Exp'.
fromExpression :: Exp a -> Control EType (Scope a) (Exp a)
fromExpression (Var a) 
