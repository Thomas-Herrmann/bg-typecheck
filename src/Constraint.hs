module Constraint
  ( Constraint (..),
  )
where

import Index (Index)

-- represents I <= J
newtype Constraint = Constraint (Index, Index)

instance Show Constraint where
  show (Constraint (ixI, ixJ)) = show ixI ++ " <= " ++ show ixJ