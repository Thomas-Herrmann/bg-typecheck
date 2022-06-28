module Main where

import Constraint (Constraint (..), NormalizedConstraint (..))
import Data.List (intercalate)
import qualified Data.Map as Map
import Data.Set as Set
import GHC.IO.Encoding
import Index
import Intervals (checkJudgement)
import Normalization (normalizeConstraint, normalizeIndex)
import PiCalculus
import SType
import STypeCheck

main :: IO ()
main = do
  putStrLn ""
  putStrLn "Process: !npar(n).match n { 0 -> 0; s(m) -> npar<m> | tick.0 } | npar<10>"
  putStrLn "Type context: "
  putStrLn "    npar : \\forall_0 i,j. serv_j^{in,out}(Nat[0,j])"
  nparProcRes <- checkProcess Set.empty Set.empty combinedGamma nparProc
  putStrLn $ "Result: " ++ show nparProcRes
  putStrLn ""
  putStrLn ""
  putStrLn "Process: !seq(n,r).match n { 0 -> r<>; s(m) :-> tick.seq<m,r> } | (vr')(seq<10,r> | r'().0)"
  putStrLn "Type context: "
  putStrLn "    seq : \\forall_0 i,j,k. serv^{in,out}_i(Nat[0,i],ch^{out}_i())"
  seqProcRes <- checkProcess Set.empty Set.empty combinedGamma seqProc
  putStrLn $ "Result: " ++ show seqProcRes
  putStrLn ""
  putStrLn ""
  putStrLn "Process: !seqSq(n).match n { 0 -> 0; s(m) -> (vr)(seq<m, r> | r().seqSq<m> ) } | seqSq<9>"
  putStrLn "Type context: "
  putStrLn "      seq : \\forall_0 i,j,k. serv^{in,out}_i(Nat[0,i],ch^{out}_i())"
  putStrLn "    seqSq : \\forall_0 l,j.serv^{in,out}_{j*j}(Nat[0,j])"
  seqSqProcRes <- checkProcess Set.empty Set.empty combinedGamma seqSqProc
  putStrLn $ "Result: " ++ show seqSqProcRes
  putStrLn ""
  putStrLn ""
  putStrLn "Process: !add(x, y, r).match x {0 -> r<y>; succ(z) -> tick.add<z, succ(yp), r>} | (vr')(add<12,30,r'> | r'(v).0)"
  putStrLn "Type context: "
  putStrLn "    add : \\forall_0 i,j,k,l,m,n,o. serv_j^{in,out}(Nat[0,j], Nat[0,l], ch_j^{out}(Nat[0, j+l]))"
  addProcRes <- checkProcess Set.empty Set.empty combinedGamma addProc
  putStrLn $ "Result: " ++ show addProcRes
  putStrLn ""

nparProc =
  nparServProc :|: OutputP "npar" [natExp 10]

seqProc =
  seqServProc
    :|: RestrictP
      "r'"
      (ChST (nIndex 10) [] inOutCap)
      (OutputP "seq" [natExp 10, VarE "r'"] :|: InputP "r'" ["v"] NilP)

seqSqProc =
  seqServProc :|: OutputP "seqSq" [natExp 9]

addProc =
  addServProc
    :|: RestrictP
      "r"
      (ChST (nIndex 12) [NatST (nIndex 42) (nIndex 42)] inOutCap)
      (OutputP "add" [natExp 12, natExp 30, VarE "r"] :|: InputP "r" ["v"] NilP)

[inCap, outCap, inOutCap] = [Set.singleton InputC, Set.singleton OutputC, Set.fromList [InputC, OutputC]]

i : j : k : l : m : n : o : rest = [0 ..]

[iM, jM, kM, lM, mM, nM, ijM, jjM] = [[i], [j], [k], [l], [m], [n], [i, j], [j, j]]

nparServProc =
  RepInputP
    "npar"
    ["n"]
    ( MatchNatP
        (VarE "n")
        NilP
        "m"
        (OutputP "npar" [VarE "m"] :|: TickP NilP)
    )

-- !seq(n,r).match n { 0 :-> r<>; s(m) :-> tick.seq<m,r> }
seqServProc =
  RepInputP
    "seq"
    ["n", "r"]
    ( MatchNatP
        (VarE "n")
        (OutputP "r" [])
        "m"
        ( TickP $
            OutputP "seq" [VarE "m", VarE "r"]
        )
    )

-- !seqSq(n).match n { 0 :-> 0; s(m) :-> (vr)(seq<m, r> | r().seqSq<m> ) }
seqSqServProc =
  seqServProc
    :|: RepInputP
      "seqSq"
      ["n"]
      ( MatchNatP
          (VarE "n")
          NilP
          "m"
          ( RestrictP
              "r"
              (ChST (monIndex jM 1 .-. nIndex 1) [] inOutCap)
              (OutputP "seq" [VarE "m", VarE "r"] :|: InputP "r" [] (OutputP "seqSq" [VarE "m"]))
          )
      )

-- !add(x, y, r).match x {0 -> r<y>; succ(z) -> tick.add<z, succ(yp), r>}
addServProc =
  RepInputP
    "add"
    ["x", "y", "r"]
    ( MatchNatP
        (VarE "x")
        (OutputP "r" [VarE "y"])
        "z"
        (TickP $ OutputP "add" [VarE "z", SuccE (VarE "y"), VarE "r"])
    )

combinedGamma =
  Map.fromList
    [ ("npar", nparType),
      ("add", addType),
      ("seq", seqType),
      ("seqSq", seqSqType)
    ]
  where
    -- npar: \forall_0 i,j. serv_j^{in,out}(Nat[0,j])
    nparType =
      ServST
        zeroIndex
        [i, j]
        (nIndex 1)
        [NatST zeroIndex (monIndex jM 1)]
        inOutCap

    -- add: \forall_0 i,j,k,l,m,n,o. serv_j^{in,out}(Nat[0,j], Nat[0,l], ch_j^{out}(Nat[0, j+l]))
    addType =
      ServST
        zeroIndex
        [i, j, k, l, m, n, o]
        (monIndex jM 1)
        [ NatST zeroIndex (monIndex jM 1),
          NatST zeroIndex (monIndex lM 1),
          ChST
            (monIndex jM 1)
            [NatST zeroIndex (monIndex jM 1 .+. monIndex lM 1)]
            outCap
        ]
        inOutCap

    -- seq: \forall_0 i,j,k. serv^{in,out}_i(Nat[0,i],ch^{out}_i())
    seqType =
      ServST
        zeroIndex
        [i, j, k]
        (monIndex jM 1)
        [ NatST zeroIndex (monIndex jM 1),
          ChST
            (monIndex jM 1)
            []
            outCap
        ]
        inOutCap

    -- seqSq : \forall_0 l,j.serv^{in,out}_{j*j}(Nat[0,j])
    seqSqType =
      ServST
        zeroIndex
        [l, j]
        (monIndex jjM 1)
        [NatST zeroIndex (monIndex jM 1)]
        inOutCap

makeConstraint ixI ixJ = head . Set.toList . normalizeConstraint $ normalizeIndex ixI :<=: normalizeIndex ixJ

testConstraint = makeConstraint ((VarI 0 :+: NatI 10) :*: (VarI 1 :-: NatI 5)) (NatI 10 :*: (VarI 0 :+: VarI 1))

testConstraint' = makeConstraint (VarI 0 :+: NatI 1) ((VarI 0 :*: VarI 1) :-: (NatI 51 :+: (VarI 0 :*: NatI 7)))

newConstraint = makeConstraint ((VarI 0 :*: NatI 10) :+: NatI 10) (NatI 100 :*: (VarI 0 :+: VarI 1))

newConstraint' = makeConstraint ((VarI 0 :*: NatI 10) :+: (VarI 1 :*: NatI 10)) (NatI 100 :*: (VarI 0 :+: VarI 1))

--main :: IO ()
--main = do
--  setLocaleEncoding utf8
--  let judgement1 = showJudgement (Set.singleton 0) (Set.fromList [testConstraint, testConstraint']) newConstraint
--  let judgement2 = showJudgement (Set.singleton 0) (Set.fromList [testConstraint, testConstraint']) newConstraint'
--  writeFile "judgements.txt" $ judgement1 ++ "\n\n" ++ judgement2

showJudgement :: Set VarID -> Set NormalizedConstraint -> NormalizedConstraint -> String
showJudgement vphi phi c = vphiString ++ "\n" ++ phiString ++ "\nφ;Φ" ++ turnstile ++ show c
  where
    vphiString = "φ={i" ++ intercalate ", " (Prelude.map (("i" ++) . show) (Set.toAscList vphi)) ++ "}"
    phiString = "Φ={" ++ intercalate ", " (Prelude.map show (Set.toAscList phi)) ++ "}"
    turnstile = if checkJudgement vphi phi c then " ⊨ " else " ⊭ "