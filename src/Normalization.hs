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

expandIndex :: Index -> [(Integer, MultiSet VarID)]
expandIndex (NatI n) = [(naturalToInteger n, MultiSet.empty)]
expandIndex (VarI i) = [(1, MultiSet.singleton i)]
expandIndex (ixI :+: ixJ) = expandIndex ixI ++ expandIndex ixJ
expandIndex (ixI :-: ixJ) = expandIndex ixI ++ Prelude.map (Data.Bifunctor.first (* (-1))) (expandIndex ixJ)
expandIndex (ixI :*: ixJ) = [(n * m, ims `MultiSet.union` ims') | (n, ims) <- ixI', (m, ims') <- ixJ']
  where
    ixI' = expandIndex ixI
    ixJ' = expandIndex ixJ

normalizeIndex :: Index -> NormalizedIndex
normalizeIndex = Prelude.foldr (\(n, ims) -> Map.insertWith (+) ims n) Map.empty . expandIndex

normalize :: Constraint -> Constraint
normalize (f :<=: f') = Map.map (`div` divisor) f :<=: Map.map (`div` divisor) f'
  where
    divisor = multiGCD $ Map.elems f ++ Map.elems f'

multiGCD :: [Integer] -> Integer
multiGCD [] = 1
multiGCD (n : ns) = Prelude.foldr gcd n ns
