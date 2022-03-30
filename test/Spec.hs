import Constraint
import ConstraintInclusion
import Data.Set as Set
import Index (monIndex, nIndex, zeroIndex, (.+.))
import Normalization

main :: IO ()
main = do
  print (monIndex [1, 1, 0] 10)
  print c1
  print c2
  print c3
  print cnew
  print (constraintsInclude (Set.fold Set.union Set.empty $ Set.fromList [c1, c2, c3]) cnew)
  print $ findConical (Set.fromList []) [0, 0]
  print $ findConical (Set.fromList [[0, 0]]) [0, 1]
  print $ findConical (Set.fromList [[0, 1]]) [0, 3]
  print $ findConical (Set.fromList [[0, -1]]) [0, -3]
  print $ findConical (Set.fromList [[1, 1]]) [0, 3]
  print $ findConical (Set.fromList [[-1, -1]]) [0, -3]
  print $ findConical (Set.fromList [[0, 1, 0], [1, 0, 0]]) [2, 3, 1]
  print $ findConical (Set.fromList [[1, 0, 0, -3], [0, 1, 1, -2], [0, 0, -1, 0]]) [2, 3, 2, -15]
  print $ generateUnivariateConstraints ((head . toList . normalizeConstraint) cnew)

i = [0]

j = [1]

k = [2]

ij = [0, 1]

c1 = normalizeConstraint $ monIndex i 1 .+. nIndex (-3) :<=: zeroIndex -- 1i - 3 <= 0

c2 = normalizeConstraint $ monIndex j 1 .+. monIndex k 1 .+. nIndex (-2) :<=: zeroIndex -- 1j + 1k - 2 <= 0

c3 = normalizeConstraint $ monIndex k (-1) :<=: zeroIndex -- -1k <= 0

cnew = monIndex i 2 .+. monIndex j 3 .+. monIndex k 2 .+. nIndex (-15) :<=: zeroIndex -- 2i + 3j + 2k -15 <= 0
