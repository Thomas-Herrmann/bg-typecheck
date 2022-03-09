module Main where

import Constraint (Constraint (..), NormalizedConstraint (..))
import Data.List (intercalate)
import Data.Set as Set
import GHC.IO.Encoding
import Index (Index (..), VarID)
import Intervals (checkJudgement)
import Normalization (normalizeIndex, normalizeConstraint)

makeConstraint ixI ixJ = head . Set.toList . normalizeConstraint $ normalizeIndex ixI :<=: normalizeIndex ixJ

testConstraint = makeConstraint ((VarI 0 :+: NatI 10) :*: (VarI 1 :-: NatI 5)) (NatI 10 :*: (VarI 0 :+: VarI 1))

testConstraint' = makeConstraint (VarI 0 :+: NatI 1) ((VarI 0 :*: VarI 1) :-: (NatI 51 :+: (VarI 0 :*: NatI 7)))

newConstraint = makeConstraint ((VarI 0 :*: NatI 10) :+: NatI 10) (NatI 100 :*: (VarI 0 :+: VarI 1))

newConstraint' = makeConstraint ((VarI 0 :*: NatI 10) :+: (VarI 1 :*: NatI 10)) (NatI 100 :*: (VarI 0 :+: VarI 1))

main :: IO ()
main = do
  setLocaleEncoding utf8
  let judgement1 = showJudgement (Set.singleton 0) (Set.fromList [testConstraint, testConstraint']) newConstraint
  let judgement2 = showJudgement (Set.singleton 0) (Set.fromList [testConstraint, testConstraint']) newConstraint'
  writeFile "judgements.txt" $ judgement1 ++ "\n\n" ++ judgement2

showJudgement :: Set VarID -> Set NormalizedConstraint -> NormalizedConstraint -> String
showJudgement vphi phi c = vphiString ++ "\n" ++ phiString ++ "\nφ;Φ" ++ turnstile ++ show c
  where
    vphiString = "φ={i" ++ intercalate ", " (Prelude.map (("i" ++) . show) (Set.toAscList vphi)) ++ "}"
    phiString = "Φ={" ++ intercalate ", " (Prelude.map show (Set.toAscList phi)) ++ "}"
    turnstile = if checkJudgement vphi phi c then " ⊨ " else " ⊭ "