module Normalization
  ( makeConstraint,
    normalize,
  )
where

import Constraint (Constraint (..), constraintCoeffs)
import Data.Bifunctor
import Data.List (sort)
import Data.Map as Map
import Data.MultiSet as MultiSet
import Data.Set as Set
import GHC.Natural (Natural, naturalToInteger)
import Index (Index (..), NormalizedIndex, VarID, oneIndex, zeroIndex)

makeConstraint :: Index -> Index -> Set Constraint
makeConstraint ixI ixJ = normalize $ normalizeIndex ixI :<=: normalizeIndex ixJ

normalizeIndex :: Index -> NormalizedIndex
normalizeIndex (NatI n) = Map.singleton MultiSet.empty $ naturalToInteger n
normalizeIndex (VarI i) = Map.singleton (MultiSet.singleton i) 1
normalizeIndex (ixI :+: ixJ) = Map.unionWith (+) (normalizeIndex ixI) (normalizeIndex ixJ)
normalizeIndex (ixI :-: ixJ) = Map.unionWith (+) (normalizeIndex ixI) (Map.map (* (-1)) (normalizeIndex ixJ))
normalizeIndex (ixI :*: ixJ) = Map.fromListWith (+) [(ims `MultiSet.union` ims', n * m) | (ims, n) <- Map.assocs f, (ims', m) <- Map.assocs f']
  where
    f = normalizeIndex ixI
    f' = normalizeIndex ixJ

normalize :: Constraint -> Set Constraint
normalize c = Set.map (normalizeConstraintDivisor . normalizeConstraintInequality) (normalizeConstraintRelation c)

normalizeConstraintRelation :: Constraint -> Set Constraint
normalizeConstraintRelation (i :<=: j) = Set.singleton $ i :<=: j
normalizeConstraintRelation (i :>=: j) = Set.singleton $ j :<=: j
normalizeConstraintRelation (i :<: j) = Set.singleton $ i :<=: (j .+. oneIndex)
normalizeConstraintRelation (i :>: j) = Set.singleton $ j :<=: (i .+. oneIndex)
normalizeConstraintRelation (i :=: j) = Set.fromList [i :<=: j, j :<=: j]

normalizeConstraintInequality :: Constraint -> Constraint
normalizeConstraintInequality = applyOnCon (\(i, j) -> (i .-. j, zeroIndex))

normalizeConstraintDivisor :: Constraint -> Constraint
normalizeConstraintDivisor c = applyOnCon (\(i, j) -> (i ./. d, j ./. d)) c
  where
    d = multiGCD (constraintCoeffs c)

multiGCD :: [Integer] -> Integer
multiGCD [] = 1
multiGCD (n : ns) = Prelude.foldr gcd n ns

-- Transforms a constraint without changing the relation sign
applyOnCon :: ((NormalizedIndex, NormalizedIndex) -> (NormalizedIndex, NormalizedIndex)) -> Constraint -> Constraint
applyOnCon f (i :<=: j) = i' :<=: j' where (i', j') = f (i, j)
applyOnCon f (i :>=: j) = i' :>=: j' where (i', j') = f (i, j)
applyOnCon f (i :<: j) = i' :<: j' where (i', j') = f (i, j)
applyOnCon f (i :>: j) = i' :>: j' where (i', j') = f (i, j)
applyOnCon f (i :=: j) = i' :=: j' where (i', j') = f (i, j)
