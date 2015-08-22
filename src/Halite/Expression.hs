module Halite.Expression where

-- | A human-readable identifier for a variable.
data Symbol = Atom String

-- | A syntax tree for a typed lamba term with variables of type @a@ that
-- includes annotations for human readibility.
data Exp a

    -- | A reference to a variable.
    = Var a

    -- | A function application.
    | App (Exp a) (Exp a)

    -- | An explicit lambda abstraction.
    | Lam Symbol (Exp (Maybe a))

    -- | A placeholder for a value which has not yet been defined.
    | Hole
