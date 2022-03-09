module SType
  ( SType (..),
    BType (..),
    IOCapability (..),
  )
where

import Data.Set
import Index (NormalizedIndex (..), VarID)

data IOCapability = InputC | OutputC deriving (Eq)

data BType
  = NatBT NormalizedIndex NormalizedIndex
  | ListBT NormalizedIndex NormalizedIndex BType

data SType
  = BaseST BType
  | ChST NormalizedIndex [SType] (Set IOCapability)
  | ServST NormalizedIndex [VarID] NormalizedIndex [SType] (Set IOCapability)