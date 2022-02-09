module ConstraintInclusion
  ( constraintsInclude,
  )
where

import Constraint (transitiveClosure, Constraint, subConstraint)
import Normalization (normalize)
import Data.Set as Set


constraintsInclude :: Set Constraint -> Constraint -> Bool
constraintsInclude phi constraint = Set.foldr (\constraint'' b -> subConstraint constraint' constraint'' || b) False phi'
  where
    phi' = transitiveClosure $ Set.map normalize phi
    constraint' = normalize constraint