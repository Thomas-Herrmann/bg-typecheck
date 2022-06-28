import Constraint
import ConstraintInclusion
import Data.Map as Map
import Data.Set as Set
import Index
import Normalization
import PiCalculus
import SType
import STypeCheck
import Test.Hspec

normSingle = head . Set.toList . normalizeConstraint

constraintInclusionSpec = describe "constraintInclusion" $ do
  it "should invert constraint i >= 5 to i - 4 <= 0" $ do
    invertConstraint (normSingle (monIndex iM 1 :>=: nIndex 5)) `shouldBe` normSingle (monIndex iM 1 .+. nIndex (-4) :<=: zeroIndex)
  it "should invert constraint 2i + 3j + 2k -15 <= 0 to -2i + -3j + -2k + 16 <= 0" $ do
    invertConstraint (normSingle (monIndex iM 2 .+. monIndex jM 3 .+. monIndex kM 2 .+. nIndex (-15) :<=: zeroIndex))
      `shouldBe` normSingle (monIndex iM (-2) .+. monIndex jM (-3) .+. monIndex kM (-2) .+. nIndex 16 :<=: zeroIndex)
  it "should generate univariate constraints 1i -3 <= 0 and 1j -3 <= 0 from 1i + 1j -3 <= 0" $ do
    generateUnivariateConstraints (normSingle cnew)
      `shouldBe` Set.fromList [normSingle ((monIndex iM 1 .+. nIndex (-3)) :<=: zeroIndex), normSingle ((monIndex jM 1 .+. nIndex (-3)) :<=: zeroIndex)]
  it "should verify constraint judgement {i};{i <= 5} |= {i - 5 <= 0}" $ do
    constraintsInclude (Set.fromList [normSingle (monIndex iM 1 :<=: nIndex 5)]) (monIndex iM 1 .+. nIndex (-5) :<=: zeroIndex)
      `shouldBe` True
  it "should NOT verify constraint judgement {i};{} |= {i - 5 <= 0}" $ do
    constraintsInclude Set.empty (monIndex iM 1 .+. nIndex (-5) :<=: zeroIndex)
      `shouldBe` False
  -- Example 3.3.3 in the paper
  it "should check constraint judgement {i, j, k};{3i - 3 <= 0, 1j + 2k - 2 <= 0, -1k <= 0} |= i + j - 3 <= 0" $ do
    constraintsInclude (Set.fold Set.union Set.empty $ Set.fromList [c1, c2, c3]) cnew `shouldBe` True

constraintInclusionZ3Spec = describe "constraintInclusionZ3" $ do
  it "[Z3] should invert constraint i >= 5 to i - 4 <= 0" $ do
    constraintsIncludeZ3 (Set.fromList [normSingle (monIndex iM 1 :<=: nIndex 5)]) (monIndex iM 1 .+. nIndex (-5) :<=: zeroIndex)
      `shouldReturn` True
  it "[Z3] should NOT verify constraint judgement {i};{} |= {i - 5 <= 0}" $ do
    constraintsIncludeZ3 Set.empty (monIndex iM 1 .+. nIndex (-5) :<=: zeroIndex)
      `shouldReturn` False
  -- Example 3.3.3 in the paper
  it "[Z3] should check constraint judgement {i, j, k};{3i - 3 <= 0, 1j + 2k - 2 <= 0, -1k <= 0} |= i + j - 3 <= 0" $ do
    constraintsIncludeZ3 (Set.fold Set.union Set.empty $ Set.fromList [c1, c2, c3]) cnew `shouldReturn` True

typeCheckSpec = describe "typeCheck" $ do
  -- Example 3.3.2 in the paper
  it "should check add process" $ do
    checkProcess Set.empty Set.empty combinedGamma addServProc `shouldReturn` Right zeroIndex
  -- Example 3.3.2 in the paper
  it "should check called add process" $ do
    checkProcess Set.empty Set.empty combinedGamma proc1 `shouldReturn` Right (nIndex 10)
  it "should check seq process" $ do
    checkProcess Set.empty Set.empty combinedGamma seqServProc `shouldReturn` Right zeroIndex
  it "should check called seq process" $ do
    checkProcess Set.empty Set.empty combinedGamma proc2 `shouldReturn` Right (nIndex 10)
  it "should check seqSq process" $ do
    checkProcess Set.empty Set.empty combinedGamma seqSqServProc `shouldReturn` Right zeroIndex
  it "should check called seqSq process" $ do
    checkProcess Set.empty Set.empty combinedGamma (seqServProc :|: OutputP "seqSq" [natExp 9]) `shouldReturn` Right (nIndex 81)

main :: IO ()
main = do
  hspec constraintInclusionSpec
  hspec constraintInclusionZ3Spec
  hspec typeCheckSpec

i : j : k : l : m : n : o : rest = [0 ..]

[iM, jM, kM, lM, mM, nM, ijM, jjM] = [[i], [j], [k], [l], [m], [n], [i, j], [j, j]]

c1 = normalizeConstraint $ monIndex iM 3 .+. nIndex (-3) :<=: zeroIndex -- 3i - 3 <= 0

c2 = normalizeConstraint $ monIndex jM 1 .+. monIndex kM 2 .+. nIndex (-2) :<=: zeroIndex -- 1j + 2k - 2 <= 0

c3 = normalizeConstraint $ monIndex kM (-1) :<=: zeroIndex -- -1k <= 0

cnew = monIndex iM 1 .+. monIndex jM 1 .+. nIndex (-3) :<=: zeroIndex -- 1i + 1j -3 <= 0

[inCap, outCap, inOutCap] = [Set.singleton InputC, Set.singleton OutputC, Set.fromList [InputC, OutputC]]

proc1 =
  addServProc
    :|: RestrictP
      "r"
      (ChST (nIndex 10) [NatST (nIndex 15) (nIndex 15)] inOutCap)
      (OutputP "add" [natExp 10, natExp 5, VarE "r"] :|: InputP "r" ["v"] NilP)

proc2 =
  seqServProc
    :|: RestrictP
      "r"
      (ChST (nIndex 10) [] inOutCap)
      (OutputP "seq" [natExp 10, VarE "r"] :|: InputP "r" ["v"] NilP)

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

combinedGamma =
  Map.fromList
    [ ("add", addType),
      ("seq", seqType),
      ("seqSq", seqSqType)
    ]
  where
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
