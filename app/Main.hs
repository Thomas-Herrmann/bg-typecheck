module Main where

import Constraint (Constraint (..))
import Index (Index (..))
import Normalization (normalize)

testixI = AddI (FacI 10 (NatI 10)) (FacI 5 (AddI (AddI (NatI 4) (NatI 5)) (VarI 0)))

testIxJ = FacI 10 (VarI 1)

testConstraint = Constraint (testixI, testIxJ)

main :: IO ()
main = print testConstraint >> print (normalize testConstraint)
