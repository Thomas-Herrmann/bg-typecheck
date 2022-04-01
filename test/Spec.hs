import Constraint
import ConstraintInclusion
import Data.Map as Map
import Data.Set as Set
import Index
import Normalization
import PiCalculus
import SType
import STypeCheck

main :: IO ()
main = do
  --print (monIndex [1, 1, 0] 10)
  --print c1
  --print c2
  --print c3
  --print cnew
  --print (constraintsInclude (Set.fold Set.union Set.empty $ Set.fromList [c1, c2, c3]) cnew)
  --print $ findConical (Set.fromList []) [0, 0]
  --print $ findConical (Set.fromList [[0, 0]]) [0, 1]
  --print $ findConical (Set.fromList [[0, 1]]) [0, 3]
  --print $ findConical (Set.fromList [[0, -1]]) [0, -3]
  --print $ findConical (Set.fromList [[1, 1]]) [0, 3]
  --print $ findConical (Set.fromList [[-1, -1]]) [0, -3]
  --print $ findConical (Set.fromList [[0, 1, 0], [1, 0, 0]]) [2, 3, 1]
  --print $ findConical (Set.fromList [[1, 0, 0, -3], [0, 1, 1, -2], [0, 0, -1, 0]]) [2, 3, 2, -15]
  --print $ generateUnivariateConstraints ((head . Set.toList . normalizeConstraint) cnew)
  putStrLn $ case checkProcess Set.empty Set.empty addProcGamma addProc of
    Left err -> err
    Right res -> show res
  putStrLn $ case checkProcess Set.empty Set.empty addProcGamma proc1 of
    Left err -> err
    Right res -> show res

i : j : k : l : m : n : o : rest = [0 ..]

[iM, jM, kM, lM, ijM] = [[i], [j], [k], [l], [i, j]]

c1 = normalizeConstraint $ monIndex iM 1 .+. nIndex (-3) :<=: zeroIndex -- 1i - 3 <= 0

c2 = normalizeConstraint $ monIndex jM 1 .+. monIndex kM 1 .+. nIndex (-2) :<=: zeroIndex -- 1j + 1k - 2 <= 0

c3 = normalizeConstraint $ monIndex kM (-1) :<=: zeroIndex -- -1k <= 0

cnew = monIndex iM 2 .+. monIndex jM 3 .+. monIndex kM 2 .+. nIndex (-15) :<=: zeroIndex -- 2i + 3j + 2k -15 <= 0

[inCap, outCap, inOutCap] = [Set.singleton InputC, Set.singleton OutputC, Set.fromList [InputC, OutputC]]

proc1 =
  addProc
    :|: RestrictP
      "r"
      (ChST (nIndex 10) [BaseST $ NatBT (nIndex 15) (nIndex 15)] inOutCap)
      (OutputP "add" [natExp 10, natExp 5, VarE "r"] :|: nTick 9 (InputP "r" ["v"] NilP))

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