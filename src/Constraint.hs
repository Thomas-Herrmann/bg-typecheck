module Constraint
  ( Constraint (..),
    NormalizedConstraint (..),
    Constraint.isUnivariate,
  )
where

import Data.Set as Set
import Index (Index, NormalizedIndex, VarID, indexCoeffs, indexVariables, isUnivariate, showNormalizedIndex, subIndex)

data Constraint
  = NormalizedIndex :<=: NormalizedIndex
  | NormalizedIndex :>=: NormalizedIndex
  | NormalizedIndex :=: NormalizedIndex
  deriving (Eq, Ord)

newtype NormalizedConstraint = NormalizedConstraint NormalizedIndex deriving (Eq, Ord)

instance Show Constraint where
  show (f :<=: f') = showNormalizedIndex f ++ " <= " ++ showNormalizedIndex f'
  show (f :>=: f') = showNormalizedIndex f ++ " >= " ++ showNormalizedIndex f'
  show (f :=: f') = showNormalizedIndex f ++ " == " ++ showNormalizedIndex f'

instance Show NormalizedConstraint where
  show (NormalizedConstraint ixI) = show ixI

indexVariables :: NormalizedConstraint -> Set VarID
indexVariables (NormalizedConstraint ix) = Index.indexVariables ix

isUnivariate :: NormalizedConstraint -> Bool
isUnivariate (NormalizedConstraint ix) = Index.isUnivariate ix