{-# LANGUAGE FlexibleInstances #-}

module Index
  ( Index (..),
    NormalizedIndex,
    equalsConstant,
    evaluate,
    substituteVar,
    substituteVars,
    indexCoeffs,
    indexVariables,
    zeroIndex,
    oneIndex,
    subIndex,
    nIndex,
    monIndex,
    VarID,
    showNormalizedIndex,
    (.+.),
    (.-.),
    (.*.),
    (./.),
    Subst,
    Monomial,
    indexMonomials,
    isUnivariate,
    degree,
    adjustMonus,
  )
where

import Data.List (intercalate)
import Data.List as List
import Data.Map as Map
import Data.MultiSet as MultiSet
import Data.Set as Set
import GHC.Natural (Natural, naturalToInt)

type VarID = Int

type Subst = Map VarID NormalizedIndex

data Index = NatI Natural | VarI VarID | Index :+: Index | Index :-: Index | Index :*: Index deriving (Eq, Ord)

type Monomial = MultiSet VarID

type NormalizedIndex = Map Monomial Double

instance Show Index where
  show (NatI n) = show n
  show (VarI i) = "i" ++ show i
  show (ixI :+: ixJ) = "(" ++ show ixI ++ "+" ++ show ixJ ++ ")"
  show (ixI :-: ixJ) = "(" ++ show ixI ++ "-" ++ show ixJ ++ ")"
  show (ixI :*: ixJ) = show ixI ++ show ixJ

instance {-# OVERLAPPING #-} Show NormalizedIndex where
  show ix = "{" ++ showNormalizedIndex ix ++ "}"

equalsConstant ix c = Map.size ix == 1 && Map.lookup MultiSet.empty ix == Just c

evaluate :: NormalizedIndex -> Map VarID Double -> Maybe Double
evaluate f subst = Map.foldrWithKey (\monomial coeff res -> instantiate monomial >>= (\prod -> res >>= (\sum -> Just (coeff * prod + sum)))) (Just 0) f
  where
    instantiate = MultiSet.fold (\i mProd -> Map.lookup i subst >>= (\n -> mProd >>= (\prod -> Just (n * prod)))) $ Just 1

substituteVar :: NormalizedIndex -> VarID -> NormalizedIndex -> NormalizedIndex
substituteVar ixI var ixJ = Map.foldrWithKey (\monomial coeff res -> monomialSubstitute monomial coeff var ixJ .+. res) zeroIndex ixI
  where
    monomialSubstitute :: Monomial -> Double -> VarID -> NormalizedIndex -> NormalizedIndex
    monomialSubstitute monomial coeff var ixJ = List.foldr (.*.) (Map.singleton strippedMonomial coeff) (List.concat (List.replicate varOccurences [ixJ]))
      where
        varOccurences = MultiSet.occur var monomial
        strippedMonomial = MultiSet.deleteAll var monomial

substituteVars :: NormalizedIndex -> Subst -> NormalizedIndex
substituteVars ixI subst = Prelude.foldr ((.+.) . replace) Map.empty $ Map.assocs ixI
  where
    replace (ms, n) =
      let (joint, disjoint) = MultiSet.partition (`Map.member` subst) ms
       in MultiSet.fold ((.*.) . (subst !)) (Map.singleton disjoint n) joint

indexCoeffs :: NormalizedIndex -> [Double]
indexCoeffs = Map.elems

indexMonomials :: NormalizedIndex -> Set Monomial
indexMonomials = Map.keysSet

indexVariables :: NormalizedIndex -> Set VarID
indexVariables ix = Set.fold Set.union Set.empty (Set.map MultiSet.toSet (indexMonomials ix))

zeroIndex :: NormalizedIndex
zeroIndex = Map.empty

oneIndex :: NormalizedIndex
oneIndex = Map.singleton MultiSet.empty 1

nIndex :: Double -> NormalizedIndex
nIndex = Map.singleton MultiSet.empty

monIndex :: [VarID] -> Double -> NormalizedIndex
monIndex mon = Map.singleton (MultiSet.fromList mon)

degree :: NormalizedIndex -> Int
degree = maximum . Prelude.map (\(k, _) -> MultiSet.size k) . Map.toList

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

(./.) :: NormalizedIndex -> Double -> NormalizedIndex
(./.) f1 n = Map.map (/ n) f1

showNormalizedIndex :: NormalizedIndex -> String
showNormalizedIndex f = intercalate " + " $ Prelude.map (\(ims, n) -> show n ++ Prelude.foldr (\i s -> "*i" ++ show i ++ s) "" ims) (Map.assocs f)

isUnivariate :: NormalizedIndex -> Bool
isUnivariate ix = Set.size (indexVariables ix) == 1