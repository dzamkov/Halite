module Halite.Expression where

-- | The unfixed version of 'Expression'.
data ExpressionF e a

    -- | A reference to a variable.
    = Var a

    -- | A function application.
    | App (e a) (e a)

    -- | An explicit lambda abstraction.
    | Lam (e (Maybe a))

    -- | A placeholder for a value which has yet to be defined.
    | Hole

-- | A syntax tree for a typed lamba term with variables of type @a@ that
-- includes annotations for human readibility.
newtype Expression a = Exp (ExpressionF Expression a)
