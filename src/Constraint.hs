module Constraint
  ( Constraint (..),
    NormalizedConstraint (..),
    Constraint.isUnivariate,
    invertConstraint,
    maxIndexVar,
    minDelta,
  )
where

import Data.Map as Map (map)
import Data.Set as Set
import Index (Index, NormalizedIndex, VarID, indexCoeffs, indexVariables, isUnivariate, nIndex, showNormalizedIndex, subIndex, (.+.), (.-.))

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
  show (NormalizedConstraint ixI) = show ixI ++ " <= 0"

minDelta = 1

indexVariables :: NormalizedConstraint -> Set VarID
indexVariables (NormalizedConstraint ix) = Index.indexVariables ix

isUnivariate :: NormalizedConstraint -> Bool
isUnivariate (NormalizedConstraint ix) = Index.isUnivariate ix

maxIndexVar :: Set NormalizedConstraint -> VarID
maxIndexVar phi = if Set.null phi then 0 else (maximum . Set.map (maximum . (\(NormalizedConstraint ix) -> Index.indexVariables ix))) phi

invertConstraint :: NormalizedConstraint -> NormalizedConstraint
invertConstraint (NormalizedConstraint ix) = NormalizedConstraint (Map.map negate ix .+. nIndex minDelta)