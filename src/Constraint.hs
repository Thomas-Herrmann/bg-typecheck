module Constraint
  ( Constraint (..),
    NormalizedConstraint (..),
  )
where

import Data.Set as Set
import Index (Index, NormalizedIndex, indexCoeffs, showNormalizedIndex, subIndex)


data Constraint
  = NormalizedIndex :<=: NormalizedIndex
  | NormalizedIndex :>=: NormalizedIndex
  | NormalizedIndex :<: NormalizedIndex
  | NormalizedIndex :>: NormalizedIndex
  | NormalizedIndex :=: NormalizedIndex
  deriving (Eq, Ord)

newtype NormalizedConstraint = NormalizedConstraint NormalizedIndex deriving (Eq, Ord)

instance Show Constraint where
  show (f :<=: f') = showNormalizedIndex f ++ " <= " ++ showNormalizedIndex f'
  show (f :>=: f') = showNormalizedIndex f ++ " >= " ++ showNormalizedIndex f'
  show (f :<: f') = showNormalizedIndex f ++ " < " ++ showNormalizedIndex f'
  show (f :>: f') = showNormalizedIndex f ++ " > " ++ showNormalizedIndex f'
  show (f :=: f') = showNormalizedIndex f ++ " == " ++ showNormalizedIndex f'


instance Show NormalizedConstraint where
  show (NormalizedConstraint ixI) = show ixI