module ConstraintInclusion
  (
  )
where

--constraintsInclude,

import Constraint (Constraint)
import Data.Set as Set
import Normalization (normalizeIndex)

--constraintsInclude :: Set Constraint -> Constraint -> Bool
--constraintsInclude phi constraint = Set.foldr (\constraint'' b -> subConstraint constraint' constraint'' || b) False phi'
--  where
--    phi' = transitiveClosure $ Set.map normalize phi
--    constraint' = normalize constraint