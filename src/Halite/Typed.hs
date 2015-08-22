module Halite.Typed where

type Nat = Integer

-- | A term in typed lambda calculus with variables of type @a@. The term
-- may or may not be well-typed.
data Term a
    = Var a
    | App (Term a) (Term a)
    | Lam (Term a) (Term (Maybe a))
    | All (Term a) (Term (Maybe a))
    | Star Nat
    deriving (Eq, Ord, Show)

-- | Determines whether a term is well-typed and, if so, returns its type. The
-- types of all variables must be given.
judge :: (a -> Term a) -> Term a -> Maybe (Term a)
judge var (Var x) = Just $ var x
judge _ (Star n) = Just $ Star (n + 1)
