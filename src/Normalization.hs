module Normalization
  ( makeConstraint,
    normalize,
  )
where

import Constraint (Constraint (..))
import Data.Bifunctor
import Data.List (sort)
import Data.Map as Map
import Data.MultiSet as MultiSet
import Data.Set as Set
import GHC.Natural (Natural, naturalToInteger)
import Index (Index (..), NormalizedIndex, VarID)

makeConstraint :: Index -> Index -> Constraint
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

normalize :: Constraint -> Constraint
normalize (f :<=: f') = Map.map (`div` divisor) f :<=: Map.map (`div` divisor) f'
  where
    divisor = multiGCD $ Map.elems f ++ Map.elems f'

multiGCD :: [Integer] -> Integer
multiGCD [] = 1
multiGCD (n : ns) = Prelude.foldr gcd n ns
