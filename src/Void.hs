{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE StandaloneDeriving #-}
module Void where

import Data.Monoid

-- | The empty type.
data Void
deriving instance Eq Void
deriving instance Ord Void
deriving instance Show Void
instance Monoid Void where
    mempty = undefined
    mappend = undefined
