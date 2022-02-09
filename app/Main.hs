module Main where

import Constraint (Constraint (..), transitiveClosure)
import Data.Set as Set
import Index (Index (..), Term (..))
import Normalization (normalize)
import ConstraintInclusion (constraintsInclude)

testixI = 104 :+: [4 :*: (0, [1])]
testixJ = 28 :+: [12 :*: (0, []), 8 :*: (2, [])]

testConstraint = testixI :<=: testixJ

testConstraint' = 32 :+: [16 :*: (0, []), 12 :*: (2, [])] :<=: (56 :+: [36 :*: (0, []), 12 :*: (2, [3])])

main :: IO ()
main = do
  print [testConstraint, testConstraint']
  let newConstraint = testixI :<=: (112 :+: [36 :*: (0, []), 24 :*: (2, [3])])
  print $ normalize newConstraint
  let transclo = transitiveClosure $ Set.fromList $ Prelude.map normalize [testConstraint, testConstraint']
  print $ transclo
  print $ constraintsInclude transclo newConstraint