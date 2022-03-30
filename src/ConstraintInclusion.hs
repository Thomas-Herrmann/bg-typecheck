module ConstraintInclusion
  ( constraintsInclude,
    constraintsInclude',
    findConical,
    generateUnivariateConstraints,
    generateUnivariateConstraint,
    constructLinearConstraint,
  )
where

import Constraint (Constraint ((:<=:)), NormalizedConstraint (NormalizedConstraint), isUnivariate)
import Control.Monad (when)
import Data.Array
import Data.Complex (Complex ((:+)))
import Data.Map as Map hiding (notMember)
import Data.Maybe
import Data.MultiSet as MultiSet
import Data.Set as Set hiding (notMember)
import Index (Monomial, NormalizedIndex, VarID, degree, evaluate, indexMonomials, indexVariables, monIndex, nIndex, zeroIndex, (.+.))
import Matrix.Simplex (Simplex (Optimal), twophase)
import Normalization (normalizeConstraint, normalizeIndex)
import Polynomial.Roots (roots)

type VectorizedConstraint = [Double]

constraintsInclude :: Set NormalizedConstraint -> Constraint -> Bool
constraintsInclude phi constraint = Prelude.foldr ((&&) . constraintsInclude' phi) True normalizedConstraint
  where
    normalizedConstraint = normalizeConstraint constraint

constraintsInclude' :: Set NormalizedConstraint -> NormalizedConstraint -> Bool
constraintsInclude' phi constraint =
  case findConical vectorizedPhi vectorizedCon of
    Optimal _ -> True
    _ -> False
  where
    linearizedPhi = Set.foldr Set.union Set.empty (Set.map generateUnivariateConstraints phi)
    phi' = Set.union phi linearizedPhi
    vphi = allMonomials (Set.insert constraint phi')
    vphiList = Set.toList vphi
    vectorizedPhi = Set.map (vectorizeConstraint vphiList) phi'
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
    arrayBuilder i 0 = vecCon' !! (i - 1) -- b
    arrayBuilder i j = vecPhiList'' !! (j - 1) !! (i - 1) -- A

vectorizeConstraint :: [Monomial] -> NormalizedConstraint -> VectorizedConstraint
vectorizeConstraint vphi (NormalizedConstraint ix) = Prelude.map (fromMaybe 0 . (`Map.lookup` ix)) vphi

allMonomials :: Set NormalizedConstraint -> Set Monomial
allMonomials = Prelude.foldr (\(NormalizedConstraint ix) a -> indexMonomials ix `Set.union` a) Set.empty

-- Attempts to remove terms to get univariate constraints
generateUnivariateConstraints :: NormalizedConstraint -> Set NormalizedConstraint
generateUnivariateConstraints c | isUnivariate c = Set.singleton c
generateUnivariateConstraints c@(NormalizedConstraint ix) =
  Set.map fromJust . Set.delete Nothing $ Set.map (generateUnivariateConstraint c) (indexVariables ix)

-- Tries to remove all but a particular index variable from a constraint
generateUnivariateConstraint :: NormalizedConstraint -> VarID -> Maybe NormalizedConstraint
generateUnivariateConstraint c i | isUnivariate c = Just c
generateUnivariateConstraint (NormalizedConstraint ix) i = do
  ix' <- Map.foldrWithKey foldFunc (Just Map.empty) ix
  return (NormalizedConstraint ix')
  where
    -- TODO fix the thing with constant terms
    foldFunc :: Monomial -> Double -> Maybe NormalizedIndex -> Maybe NormalizedIndex
    foldFunc monomial coeff acc = do
      acc <- acc
      when (coeff < 0 && (MultiSet.notMember i monomial || Set.size (MultiSet.toSet monomial) > 1)) Nothing
      if Set.size (MultiSet.toSet monomial) == 1
        then return acc
        else return $ acc .+. Map.singleton (insertMany i (MultiSet.occur i monomial) MultiSet.empty) coeff

constructLinearConstraint :: NormalizedConstraint -> Maybe NormalizedConstraint
constructLinearConstraint c | not (isUnivariate c) = Nothing
constructLinearConstraint (NormalizedConstraint ix) = do
  when (length rsReal /= 1) Nothing
  sign <- sign
  return (NormalizedConstraint $ Map.fromList [(MultiSet.empty, head rsReal), (MultiSet.singleton i, sign)])
  where
    i = head (Set.toList (indexVariables ix))
    monomials = Prelude.map (MultiSet.fromList . (`Prelude.take` repeat i)) [0 .. degree ix]
    p = Prelude.map (\m -> 0 :+ Map.findWithDefault 0 m ix) monomials
    rs = roots 1.0e-10 500 p
    rsReal = Prelude.map (\(a :+ b) -> b) (Prelude.filter (\(a :+ b) -> a == 0) rs)
    sign = do
      v <- Index.evaluate ix (Map.singleton i (head rsReal + 1))
      if v >= 0 then Just 1 else Just 0
