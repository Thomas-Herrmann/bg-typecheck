module ConstraintInclusion
  ( constraintsInclude,
    constraintsInclude',
    constraintsIncludeZ3,
    findConical,
    generateUnivariateConstraints,
    generateUnivariateConstraint,
    constructLinearConstraint,
  )
where

import Conduit
import Constraint (Constraint ((:<=:)), NormalizedConstraint (NormalizedConstraint), invertConstraint, isUnivariate, maxIndexVar)
import Control.Monad (foldM, replicateM, when)
import Control.Monad.ST
import Data.Array
import Data.Complex (Complex ((:+)))
import Data.Functor
import Data.Map as Map hiding (notMember)
import Data.Maybe
import Data.MultiSet as MultiSet
import Data.Set as Set hiding (notMember)
import Debug.Trace (trace)
import Index (Monomial, NormalizedIndex, VarID, degree, evaluate, indexBias, indexCoeffs, indexMonomials, indexVariables, monIndex, nIndex, oneIndex, zeroIndex, (.+.), (.-.))
import Matrix.Simplex (Simplex (Infeasible, Optimal), simplex, twophase)
import Normalization (normalizeConstraint, normalizeIndex)
import Numeric.Optimization.MIP.Base (def)
import Polynomial.Roots (roots)
import ToySolver.Arith.Simplex
import qualified ToySolver.Data.LA as LA
import Z3.Monad

type VectorizedConstraint = [Double]

constraintsIncludeZ3 :: Set NormalizedConstraint -> Constraint -> IO Bool
constraintsIncludeZ3 phi constraint = do
  bs <- mapM (evalZ3 . constraintsIncludeZ3' phi') (Set.toList normalizedConstraint)
  return $ and bs
  where
    normalizedConstraint = normalizeConstraint constraint
    phi' = Set.delete (NormalizedConstraint Map.empty) phi

constraintsIncludeZ3' :: Set NormalizedConstraint -> NormalizedConstraint -> Z3 Bool
constraintsIncludeZ3' phi constraint = do
  solveZ3 vphi phiWInvert
  where
    invConstraint = invertConstraint constraint
    linearizedPhi = Set.foldr Set.union Set.empty (Set.map generateUnivariateConstraints phi) -- Create linear constraints from polynomial constraints
    phiWInvert = Set.insert invConstraint (phi `Set.union` linearizedPhi)
    vphi = allMonomials phiWInvert -- Find vphi consisting of all index variables in phi

solveZ3 :: Set (MultiSet VarID) -> Set NormalizedConstraint -> Z3 Bool
solveZ3 vphi phi = do
  astCons <- mapM normalizedConstraintToZ3 (Set.toList phi)
  mapM_ assert astCons

  res <- Z3.Monad.check
  case res of
    Z3.Monad.Unsat -> return True
    _ -> return False

normalizedConstraintToZ3 :: NormalizedConstraint -> Z3 AST
normalizedConstraintToZ3 (NormalizedConstraint ix) = do
  _0 <- mkIntNum 0
  ast1 <- normalizedIndexToZ3 ix
  mkLe ast1 _0

normalizedIndexToZ3 :: NormalizedIndex -> Z3 AST
normalizedIndexToZ3 ix = do
  let ps = Map.assocs ix
  _0 <- mkIntNum 0
  foldM ffunc _0 ps
  where
    ffunc acc (m, c) = do
      ast1 <- monomialToZ3 m
      ast2 <- coefficientToZ3 c
      ast3 <- mkMul [ast1, ast2]
      mkAdd [acc, ast3]

monomialToZ3 :: Monomial -> Z3 AST
monomialToZ3 m = do
  _1 <- mkIntNum 1
  foldM ffunc _1 m
  where
    ffunc :: AST -> VarID -> Z3 AST
    ffunc acc v = do
      ast <- varIDToZ3 v
      mkMul [ast, acc]

varIDToZ3 :: VarID -> Z3 AST
varIDToZ3 v = do
  _0 <- mkIntNum 0
  sym <- mkIntSymbol v
  var <- mkIntVar sym
  assert =<< mkGe var _0
  return var

coefficientToZ3 :: Double -> Z3 AST
coefficientToZ3 = mkRealNum

constraintsInclude :: Set NormalizedConstraint -> Constraint -> Bool
constraintsInclude phi constraint = Prelude.foldr ((&&) . constraintsInclude' phi') True normalizedConstraint
  where
    normalizedConstraint = normalizeConstraint constraint
    phi' = Set.delete (NormalizedConstraint Map.empty) phi

constraintsInclude' :: Set NormalizedConstraint -> NormalizedConstraint -> Bool
constraintsInclude' phi constraint =
  triviallySatisfied constraint
    || ( not (triviallyNotSatisfied constraint)
           && case solveSimplexToy vphi phiWInvert of
             ToySolver.Arith.Simplex.Unsat -> True
             val -> False
       )
  where
    invConstraint = invertConstraint constraint
    linearizedPhi = Set.foldr Set.union Set.empty (Set.map generateUnivariateConstraints phi) -- Create linear constraints from polynomial constraints
    phiWInvert = Set.insert invConstraint (phi `Set.union` linearizedPhi)
    vphi = allMonomials (Set.insert invConstraint phiWInvert) -- Find vphi consisting of all index variables in phi

-- Checks if a normalized constraint is trivially satisfied by checking if all coefficients are nonpositive
triviallySatisfied :: NormalizedConstraint -> Bool
triviallySatisfied (NormalizedConstraint ix) = allNonpositive (indexCoeffs ix)
  where
    allNonpositive coeffs = all (<= 0) coeffs

-- Checks if a normalized constraint is trivially not satisfied by checking if all coefficients are positive and bias is also positive
triviallyNotSatisfied :: NormalizedConstraint -> Bool
triviallyNotSatisfied (NormalizedConstraint ix) = allPositive (indexCoeffs ix) && indexBias ix > 0
  where
    allPositive coeffs = all (> 0) coeffs

-- Adds slack variables to constraints to make them from = 0 to <= 0
-- Returns the new constraints and the new slack variables
addSlackVariables :: Set NormalizedConstraint -> (Set NormalizedConstraint, Set VarID)
addSlackVariables phi = (newPhi, Set.fromList $ Prelude.take (length phi) slackVars)
  where
    maxVar = maxIndexVar phi
    slackVars = [maxVar + 1 ..]
    phiList = Set.toList phi
    newPhi = Set.fromList $ zipWith (curry (\(NormalizedConstraint ix, v) -> NormalizedConstraint (ix .+. monIndex [v] 1))) phiList slackVars

solveSimplexToy :: Set (MultiSet VarID) -> Set NormalizedConstraint -> OptResult
solveSimplexToy vphi phi = runST $ do
  solver <- newSolver
  vars <- replicateM (Prelude.length vphiList) (newVar solver)
  setObj solver $ LA.fromTerms [(1, v) | v <- vars]
  let atoms = Set.map (constraintToAtom vars) phi
  mapM_ (assertAtom solver) atoms
  dualSimplex solver def
  where
    vphiList = Set.toList (Set.delete MultiSet.empty vphi)

    -- Separate constant term from constraint
    splitConstraint :: NormalizedConstraint -> (VectorizedConstraint, Double)
    splitConstraint (NormalizedConstraint ix) = (vectorizeConstraint vphiList (NormalizedConstraint ix), - (indexBias ix))

    -- Convert constraint to toysolver form
    constraintToAtom :: [Var] -> NormalizedConstraint -> Atom Rational
    constraintToAtom vars c@(NormalizedConstraint ix) =
      let (coeffs, bias) = splitConstraint c
          lhs = indexToExpr vars (Map.delete MultiSet.empty ix)
       in lhs .<=. LA.constant (toRational bias)

    indexToExpr :: [Var] -> NormalizedIndex -> LA.Expr Rational
    indexToExpr vars ix = LA.fromTerms [(toRational coeff, vphiIntMap Map.! mon) | (mon, coeff) <- Map.toList ix]
      where
        vphiIntMap = Map.fromList $ zip vphiList vars

solveSimplex :: Set Monomial -> Set NormalizedConstraint -> Simplex (Array (Int, Int) Double)
solveSimplex vphi phi = simplex arr
  where
    (phi', vphiSlack) = addSlackVariables phi -- Add slack variables to phi'
    vphi' = Set.union vphi (Set.map MultiSet.singleton vphiSlack) -- Add slack variables to vphi
    vphiList = Set.toList (Set.delete MultiSet.empty vphi')

    -- Separate constant term from constraint
    (vectorizedPhi, b) = unzip . Set.toList $ Set.map (\(NormalizedConstraint ix) -> (vectorizeConstraint vphiList (NormalizedConstraint ix), - (indexBias ix))) phi'

    arr = array dims [((i, j), arrayBuilder i j) | (i, j) <- range dims]
    dims = ((0, 0), (Prelude.length b, Prelude.length vphiList))

    -- Create simplex tableau
    arrayBuilder :: Int -> Int -> Double
    arrayBuilder 0 0 = -1 -- -z
    arrayBuilder 0 j = 1 -- c'
    arrayBuilder i 0 = b !! (i - 1) -- b
    arrayBuilder i j = vectorizedPhi !! (i - 1) !! (j - 1) -- A

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

-- Polynomial stuff

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
    foldFunc :: Monomial -> Double -> Maybe NormalizedIndex -> Maybe NormalizedIndex
    foldFunc monomial coeff acc = do
      acc <- acc
      when (coeff < 0 && (MultiSet.notMember i monomial && numDistinctVars monomial > 0)) Nothing -- If we see a term with negative coefficient that contains other variables than i, we can't remove it
      if numDistinctVars (MultiSet.deleteAll i monomial) > 0
        then return acc
        else return $ acc .+. Map.singleton (insertMany i (MultiSet.occur i monomial) MultiSet.empty) coeff

    numDistinctVars monomial = Set.size (MultiSet.toSet monomial)

-- Constructs a linear constraint with the same properties as a non-linear constraint
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
