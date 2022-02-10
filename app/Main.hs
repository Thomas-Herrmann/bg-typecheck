module Main where

import Constraint (Constraint (..), transitiveClosure)
import ConstraintInclusion (constraintsInclude)
import Data.List (intercalate)
import Data.Set as Set
import GHC.IO.Encoding
import Index (Index (..), Term (..), VarID)
import Normalization (normalize)

testixI = 104 :+: [4 :*: (0, [1])]

testixJ = 28 :+: [12 :*: (0, []), 8 :*: (2, [])]

testConstraint = testixI :<=: testixJ

testConstraint' = 32 :+: [16 :*: (0, []), 12 :*: (2, [])] :<=: (56 :+: [36 :*: (0, []), 12 :*: (2, [3])])

newConstraint = testixI :<=: (112 :+: [36 :*: (0, []), 24 :*: (2, [3])])

newConstraint' = testixI :<=: (112 :+: [36 :*: (1, []), 24 :*: (2, [3])])

main :: IO ()
main = do
  setLocaleEncoding utf8
  let judgement1 = showJudgement (Set.fromList [0, 1, 2, 3]) (Set.fromList [testConstraint, testConstraint']) newConstraint
  let judgement2 = showJudgement (Set.fromList [0, 1, 2, 3]) (Set.fromList [testConstraint, testConstraint']) newConstraint'
  writeFile "judgements.txt" $ judgement1 ++ "\n\n" ++ judgement2

showJudgement :: Set VarID -> Set Constraint -> Constraint -> String
showJudgement vphi phi c = vphiString ++ "\n" ++ phiString ++ "\nφ;Φ" ++ turnstile ++ show c
  where
    vphiString = "φ={" ++ intercalate ", " (Prelude.map (\i -> "i" ++ show i) (Set.toAscList vphi)) ++ "}"
    phiString = "Φ={" ++ intercalate ", " (Prelude.map show (Set.toAscList phi)) ++ "}"
    turnstile = if constraintsInclude phi c then " ⊨ " else " ⊭ "