module Normalization
  (
    normalizeIndex,
    normalizeIndex,
  )
where

import Constraint (Constraint (..), NormalizedConstraint (..))
import Data.Bifunctor
import Data.List (sort)
import Data.Map as Map
import Data.MultiSet as MultiSet
import Data.Set as Set
import GHC.Natural (Natural, naturalToInteger)
import Index (Index (..), NormalizedIndex, VarID, oneIndex, zeroIndex, (.*.), (.+.), (.-.), (./.))

 :: Index -> NormalizedIndex
normalizeIndex (NatI n) = Map.singleton MultiSet.empty $ naturalToInteger n
normalizeIndex (VarI i) = Map.singleton (MultiSet.singleton i) 1
normalizeIndex (ixI :+: ixJ) = Map.unionWith (+) (normalizeIndex ixI) (normalizeIndex ixJ)
normalizeIndex (ixI :-: ixJ) = Map.unionWith (+) (normalizeIndex ixI) (Map.map (* (-1)) (normalizeIndex ixJ))
normalizeIndex (ixI :*: ixJ) = Map.fromListWith (+) [(ims `MultiSet.union` ims', n * m) | (ims, n) <- Map.assocs f, (ims', m) <- Map.assocs f']
  where
    f = normalizeIndex ixI
    f' = normalizeIndex ixJ

normalizeConstraint :: Constraint -> Set NormalizedConstraint
normalizeConstraint (ixI :<=: ixJ) = Set.singleton $ NormalizedConstraint (ixI .-. ixJ)
normalizeConstraint (ixI :>=: ixJ) = Set.singleton $ NormalizedConstraint (ixJ .-. ixI)
normalizeConstraint (ixI :<: ixJ) = Set.singleton $ NormalizedConstraint (ixI .-. (ixJ .+. oneIndex))
normalizeConstraint (ixI :>: ixJ) = Set.singleton $ NormalizedConstraint (ixJ .-. (ixI .+. oneIndex))
normalizeConstraint (ixI :=: ixJ) = Set.fromList [NormalizedConstraint (ixI .-. ixJ), NormalizedConstraint (ixJ .-. ixI)]
