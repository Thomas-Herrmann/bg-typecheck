module Constraint
  ( Constraint (..),
    transitiveClosure,
    subConstraint,
  )
where

import Data.Set as Set
import Index (Index (..), subIndex)

-- represents I <= J
data Constraint = Index :<=: Index deriving (Eq, Ord)


instance Show Constraint where
  show (ixI :<=: ixJ) = show ixI ++ " <= " ++ show ixJ


subConstraint :: Constraint -> Constraint -> Bool
subConstraint (ixI :<=: ixJ) (ixI' :<=: ixJ') = subIndex ixI ixI' && subIndex ixJ' ixJ


transitiveClosure :: Set Constraint -> Set Constraint
transitiveClosure constraints
  | closure == constraints = constraints
  | otherwise = transitiveClosure closure
  where
    closure = constraints `union` Set.fromList [ ixI :<=: ixJ' | ixI :<=: ixJ <- Set.toList constraints, ixI' :<=: ixJ' <- Set.toList constraints, subIndex ixJ ixI']
