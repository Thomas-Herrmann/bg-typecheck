module Main where

import Constraint (Constraint (..), transitiveClosure)
import ConstraintInclusion (constraintsInclude)
import Data.List (intercalate)
import Data.Set as Set
import GHC.IO.Encoding
import Index (Index (..), VarID)
import Normalization (makeConstraint)

testConstraint = makeConstraint ((VarI 0 :+: NatI 10) :*: (VarI 1 :-: NatI 5)) (NatI 10 :*: (VarI 0 :+: VarI 1))

testConstraint' = makeConstraint (VarI 0 :+: NatI 1) ((VarI 0 :*: VarI 1) :-: (NatI 51 :+: (VarI 0 :*: NatI 7)))

newConstraint = makeConstraint ((VarI 0 :*: NatI 10) :+: NatI 10) (NatI 100 :*: (VarI 0 :+: VarI 1))

newConstraint' = makeConstraint ((VarI 0 :*: NatI 10) :+: (VarI 1 :*: NatI 10)) (NatI 100 :*: (VarI 0 :+: VarI 1))

main :: IO ()
main = do
  setLocaleEncoding utf8
  let judgement1 = showJudgement (Set.fromList [0, 1]) (Set.fromList [testConstraint, testConstraint']) newConstraint
  let judgement2 = showJudgement (Set.fromList [0, 1]) (Set.fromList [testConstraint, testConstraint']) newConstraint'
  writeFile "judgements.txt" $ judgement1 ++ "\n\n" ++ judgement2

showJudgement :: Set VarID -> Set Constraint -> Constraint -> String
showJudgement vphi phi c = vphiString ++ "\n" ++ phiString ++ "\n" ++ transString ++ "\nφ;Φ" ++ turnstile ++ show c
  where
    vphiString = "φ={" ++ intercalate ", " (Prelude.map (\i -> "i" ++ show i) (Set.toAscList vphi)) ++ "}"
    phiString = "Φ={" ++ intercalate ", " (Prelude.map show (Set.toAscList phi)) ++ "}"
    transString = "trans(Φ)={" ++ intercalate ", " (Prelude.map show (Set.toAscList $ transitiveClosure phi)) ++ "}"
    turnstile = if constraintsInclude phi c then " ⊨ " else " ⊭ "