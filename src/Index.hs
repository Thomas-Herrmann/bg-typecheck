module Index
  ( Index (..),
    NormalizedIndex,
    subIndex,
    VarID,
    showNormalizedIndex,
    (.+.),
    (.-.),
    (.*.),
    (./.),
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


(.+.) :: NormalizedIndex -> NormalizedIndex -> NormalizedIndex
(.+.) = Map.unionWith (+)

(.-.) :: NormalizedIndex -> NormalizedIndex -> NormalizedIndex
(.-.) f1 f2 = Map.unionWith (+) f1 $ Map.map (* (-1)) f2

(.*.) :: NormalizedIndex -> NormalizedIndex -> NormalizedIndex
(.*.) f1 f2 = Map.fromListWith (+) [(ims `MultiSet.union` ims', n * m) | (ims, n) <- Map.assocs f1, (ims', m) <- Map.assocs f2]

(./.) :: NormalizedIndex -> Integer -> NormalizedIndex
(./.) f1 n = Map.map (`div` n) f1


showNormalizedIndex :: NormalizedIndex -> String
showNormalizedIndex f = intercalate " + " $ Prelude.map (\(ims, n) -> show n ++ Prelude.foldr (\i s -> "*i" ++ show i ++ s) "" ims) (Map.assocs f)