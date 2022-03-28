module ConstraintInclusion
  ( constraintsInclude,
    findConical,
  )
where

import Constraint (Constraint, NormalizedConstraint (NormalizedConstraint))
import Data.Array
import Data.Map as Map
import Data.Maybe
import Data.MultiSet as MultiSet
import Data.Set as Set
import Index (Monomial, VarID, indexMonomials)
import Matrix.Simplex
import Normalization (normalizeConstraint, normalizeIndex)

type VectorizedConstraint = [Integer]

constraintsInclude :: Set Constraint -> Constraint -> Bool
constraintsInclude phi constraint = Prelude.foldr ((&&) . constraintsInclude' normalizedPhi) True normalizedConstraint
  where
    normalizedPhi = Set.foldr Set.union Set.empty (Set.map normalizeConstraint phi)
    normalizedConstraint = normalizeConstraint constraint

constraintsInclude' :: Set NormalizedConstraint -> NormalizedConstraint -> Bool
constraintsInclude' phi constraint =
  case findConical vectorizedPhi vectorizedCon of
    Optimal _ -> True
    _ -> False
  where
    vphi = allMonomials (Set.insert constraint phi)
    vphiList = Set.toList vphi
    vectorizedPhi = Set.map (vectorizeConstraint vphiList) phi
    vectorizedCon = vectorizeConstraint vphiList constraint

findConical :: Set VectorizedConstraint -> VectorizedConstraint -> Simplex (Array (Int, Int) Double)
findConical vecPhi vecCon = twophase arr
  where
    arr = array dims [((i, j), arrayBuilder i j) | (i, j) <- range dims]

    vecPhiList = Set.toList vecPhi

    -- Create slack variables
    slackVectors = Prelude.map (\n -> [if n == m then -1 else 0 | m <- [0 .. Prelude.length vecCon - 1]]) [0 .. Prelude.length vecCon - 1]

    vecPhiList' = vecPhiList ++ slackVectors

    -- Invert elements in vectors such that the RHS of constraints are non-negative
    invertMap = Prelude.map (< 0) vecCon
    applyInversion = zipWith (\p n -> (if p then - n else n)) invertMap

    vecCon' = applyInversion vecCon
    vecPhiList'' = Prelude.map applyInversion vecPhiList'

    dims = ((0, 0), (Prelude.length vecCon', Prelude.length vecPhiList''))

    -- Create simplex tableau
    arrayBuilder :: Int -> Int -> Double
    arrayBuilder 0 0 = 0 -- -z
    arrayBuilder 0 j = 0 -- c'
    arrayBuilder i 0 = fromInteger $ vecCon' !! (i - 1) -- b
    arrayBuilder i j = fromInteger $ vecPhiList'' !! (j - 1) !! (i - 1) -- A

vectorizeConstraint :: [Monomial] -> NormalizedConstraint -> VectorizedConstraint
vectorizeConstraint vphi (NormalizedConstraint ix) = Prelude.map (fromMaybe 0 . (`Map.lookup` ix)) vphi

allMonomials :: Set NormalizedConstraint -> Set Monomial
allMonomials = Prelude.foldr (\(NormalizedConstraint ix) a -> indexMonomials ix `Set.union` a) Set.empty