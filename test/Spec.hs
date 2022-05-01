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
  -- Example 3.3.2 in the paper
  it "should check add process" $ do
    checkProcess Set.empty Set.empty addProcGamma addProc `shouldBe` Right zeroIndex
  -- Example 3.3.2 in the paper
  it "should check called add process" $ do
    checkProcess Set.empty Set.empty addProcGamma proc1 `shouldBe` Right zeroIndex

main :: IO ()
main = do
  hspec constraintInclusionSpec

i : j : k : l : m : n : o : rest = [0 ..]

[iM, jM, kM, lM, ijM] = [[i], [j], [k], [l], [i, j]]

c1 = normalizeConstraint $ monIndex iM 3 .+. nIndex (-3) :<=: zeroIndex -- 3i - 3 <= 0

c2 = normalizeConstraint $ monIndex jM 1 .+. monIndex kM 2 .+. nIndex (-2) :<=: zeroIndex -- 1j + 2k - 2 <= 0

c3 = normalizeConstraint $ monIndex kM (-1) :<=: zeroIndex -- -1k <= 0

cnew = monIndex iM 1 .+. monIndex jM 1 .+. nIndex (-3) :<=: zeroIndex -- 1i + 1j -3 <= 0

[inCap, outCap, inOutCap] = [Set.singleton InputC, Set.singleton OutputC, Set.fromList [InputC, OutputC]]

proc1 =
  addProc
    :|: RestrictP
      "r"
      (ChST (nIndex 10) [BaseST $ NatBT (nIndex 15) (nIndex 15)] inOutCap)
      (OutputP "add" [natExp 10, natExp 5, VarE "r"] :|: nTick 9 (InputP "r" ["v"] NilP))

-- !add(x, y, r).match x {0 -> r<y>; succ(z) -> tick.add<z, succ(yp), r>}
addProc =
  RepInputP
    "add"
    ["x", "y", "r"]
    ( MatchNatP
        (VarE "x")
        (OutputP "r" [VarE "y"])
        "z"
        (TickP $ OutputP "add" [VarE "z", SuccE (VarE "y"), VarE "r"])
    )

-- add: A_0 i,j,k,l,m,n,o. serv_j^{in,out}(Nat[0,j], Nat[0,l], ch_j^{out}(Nat[0, j+l]))
addProcGamma =
  Map.singleton "add" $
    ServST
      zeroIndex
      [i, j, k, l, m, n, o]
      (monIndex jM 1)
      [ BaseST (NatBT zeroIndex (monIndex jM 1)),
        BaseST (NatBT zeroIndex (monIndex lM 1)),
        ChST
          (monIndex jM 1)
          [BaseST (NatBT zeroIndex (monIndex jM 1 .+. monIndex lM 1))]
          outCap
      ]
      inOutCap