module Constraint
  ( Constraint (..),
    transitiveClosure,
  )
where

import Data.Set as Set
import Index (Index (..), subIndex)

-- represents I <= J
newtype Constraint = Constraint (Index, Index) deriving (Eq)

instance Show Constraint where
  show (Constraint (ixI, ixJ)) = show ixI ++ " <= " ++ show ixJ

instance Ord Constraint where
  Constraint (ixI, ixJ) <= Constraint (ixI', ixJ') = subIndex (>=) ixI ixI' && subIndex (<=) ixJ ixJ'

transitiveClosure :: Set Constraint -> Set Constraint
transitiveClosure constraints
  | closure == constraints = constraints
  | otherwise = transitiveClosure closure
  where
    closure = constraints `union` Set.fromList [Constraint (ixI, ixJ') | Constraint (ixI, ixJ) <- Set.toList constraints, Constraint (ixI', ixJ') <- Set.toList constraints, subIndex (<=) ixJ ixI']