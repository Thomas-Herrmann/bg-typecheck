module Main where

import Constraint (Constraint (..), transitiveClosure)
import Data.Set as Set
import Index (Factor (..), Index (..), Term (..))
import Normalization (normalize)

--testixI = AddI (FacI 10 (NatI 10)) (FacI 5 (AddI (AddI (NatI 4) (NatI 5)) (VarI 0)))

testixI = (NatI 10 :*: FacI (NatI 10)) :+: ((VarI 1 :*: (NatI 5 :*: FacI (VarI 0))) :+: TerI (FacI (NatI 4)))

--testIxJ = FacI 10 (VarI 1)

testixJ = TerI $ NatI 112 :*: FacI (VarI 1)

testConstraint = Constraint (testixI, testixJ)

testConstraint' = Constraint (TerI $ NatI 148 :*: FacI (VarI 1), TerI $ VarI 2 :*: FacI (VarI 1))

main :: IO ()
main = do
  print [testConstraint, testConstraint']
  print (Prelude.map normalize [testConstraint, testConstraint'])
  print (transitiveClosure $ Set.fromList $ Prelude.map normalize [testConstraint, testConstraint'])
