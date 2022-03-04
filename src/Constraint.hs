module Constraint
  ( Constraint (..),
    NormalizedConstraint (..),
    constraintCoeffs,
    transitiveClosure,
    subConstraint,
  )
where

import Data.Set as Set
import Index (Index, NormalizedIndex, indexCoeffs, showNormalizedIndex, subIndex)

-- represents I <= J
data Constraint
  = NormalizedIndex :<=: NormalizedIndex
  | NormalizedIndex :>=: NormalizedIndex
  | NormalizedIndex :<: NormalizedIndex
  | NormalizedIndex :>: NormalizedIndex
  | NormalizedIndex :=: NormalizedIndex
  deriving (Eq, Ord)

newtype NormalizedConstraint = NormalizedConstraint NormalizedIndex deriving (Eq)

instance Show Constraint where
  show (f :<=: f') = showNormalizedIndex f ++ " <= " ++ showNormalizedIndex f'

constraintCoeffs (i :<=: j) = indexCoeffs i ++ indexCoeffs j
constraintCoeffs (i :>=: j) = indexCoeffs i ++ indexCoeffs j
constraintCoeffs (i :<: j) = indexCoeffs i ++ indexCoeffs j
constraintCoeffs (i :>: j) = indexCoeffs i ++ indexCoeffs j
constraintCoeffs (i :=: j) = indexCoeffs i ++ indexCoeffs j

subConstraint :: Constraint -> Constraint -> Bool
subConstraint (f1 :<=: f2) (f1' :<=: f2') = subIndex f1 f1' && subIndex f2' f2

transitiveClosure :: Set Constraint -> Set Constraint
transitiveClosure constraints
  | closure == constraints = constraints
  | otherwise = transitiveClosure closure
  where
    closure = constraints `union` Set.fromList [f1 :<=: f2' | f1 :<=: f2 <- Set.toList constraints, f1' :<=: f2' <- Set.toList constraints, subIndex f2 f1']
