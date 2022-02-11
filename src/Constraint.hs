module Constraint
  ( Constraint (..),
    transitiveClosure,
    subConstraint,
  )
where

import Data.Set as Set
import Index (Index, NormalizedIndex, showNormalizedIndex, subIndex)

-- represents I <= J
data Constraint = NormalizedIndex :<=: NormalizedIndex deriving (Eq, Ord)

instance Show Constraint where
  show (f :<=: f') = showNormalizedIndex f ++ " <= " ++ showNormalizedIndex f'

subConstraint :: Constraint -> Constraint -> Bool
subConstraint (f1 :<=: f2) (f1' :<=: f2') = subIndex f1 f1' && subIndex f2' f2

transitiveClosure :: Set Constraint -> Set Constraint
transitiveClosure constraints
  | closure == constraints = constraints
  | otherwise = transitiveClosure closure
  where
    closure = constraints `union` Set.fromList [f1 :<=: f2' | f1 :<=: f2 <- Set.toList constraints, f1' :<=: f2' <- Set.toList constraints, subIndex f2 f1']
