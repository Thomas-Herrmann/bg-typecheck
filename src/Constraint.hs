module Constraint
  ( Constraint,
  )
where

import Index (Index)

-- represents I <= J
type Constraint = (Index, Index)