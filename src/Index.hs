module Index
  ( Index (..),
    NormalizedIndex,
    indexCoeffs,
    zeroIndex,
    oneIndex,
    subIndex,
    VarID,
    showNormalizedIndex,
  )
where

import Data.List (intercalate)
import Data.Map as Map
import Data.MultiSet as MultiSet
import Data.Set as Set
import GHC.Natural (Natural)

type VarID = Int

data Index = NatI Natural | VarI VarID | Index :+: Index | Index :-: Index | Index :*: Index deriving (Eq, Ord)

type NormalizedIndex = Map (MultiSet VarID) Integer

instance Show Index where
  show (NatI n) = show n
  show (VarI i) = "i" ++ show i
  show (ixI :+: ixJ) = "(" ++ show ixI ++ "+" ++ show ixJ ++ ")"
  show (ixI :-: ixJ) = "(" ++ show ixI ++ "-" ++ show ixJ ++ ")"
  show (ixI :*: ixJ) = show ixI ++ show ixJ

indexCoeffs :: NormalizedIndex -> [Integer]
indexCoeffs = Map.elems

zeroIndex :: NormalizedIndex
zeroIndex = Map.empty

oneIndex :: NormalizedIndex
oneIndex = Map.singleton MultiSet.empty 1

subIndex :: NormalizedIndex -> NormalizedIndex -> Bool
subIndex f f' = Prelude.foldr foldf True $ Map.keysSet f `Set.union` Map.keysSet f'
  where
    foldf ims b =
      b
        && case (Map.lookup ims f, Map.lookup ims f') of
          (Just n, Just m) -> n <= m
          (Just n, Nothing) -> n <= 0
          (Nothing, Just m) -> m >= 0
          _ -> False -- should not happen

showNormalizedIndex :: NormalizedIndex -> String
showNormalizedIndex f = intercalate " + " $ Prelude.map (\(ims, n) -> show n ++ Prelude.foldr (\i s -> "*i" ++ show i ++ s) "" ims) (Map.assocs f)