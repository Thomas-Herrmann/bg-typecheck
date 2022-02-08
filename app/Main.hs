module Main where

import Constraint (Constraint (..), transitiveClosure)
import Data.Set as Set
import Index (Factor (..), Index (..), Term (..))
import Normalization (normalize)

--testixI = AddI (FacI 10 (NatI 10)) (FacI 5 (AddI (AddI (NatI 4) (NatI 5)) (VarI 0)))

--testIxJ = FacI 10 (VarI 1)

--testConstraint = Constraint (testixI, testIxJ)

--testConstraint' = Constraint (FacI 11 (VarI 1), FacI 12 (VarI 1))

main :: IO ()
main = print "todo"

--print [testConstraint, testConstraint']
--print (Prelude.map normalize [testConstraint, testConstraint'])
--print (transitiveClosure $ Set.fromList $ Prelude.map normalize [testConstraint, testConstraint'])
