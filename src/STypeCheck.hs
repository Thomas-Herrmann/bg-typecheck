module STypeCheck
  (
  )
where

import Constraint (Constraint (..), NormalizedConstraint (..))
import ConstraintInclusion (constraintsInclude)
import Data.Map as Map
import Data.Set as Set
import Index (NormalizedIndex, VarID, equalsConstant, evaluate, oneIndex, substituteVars, zeroIndex, (.*.), (.+.), (.-.), (./.))
import Intervals (checkJudgement)
import Normalization (normalizeConstraint, normalizeIndex)
import PiCalculus (Exp (..), Proc (..), Var)
import SType (BType (..), IOCapability (..), SType (..), substituteVars)

type Context = Map Var SType

inOutCapa = Set.fromList [InputC, OutputC]

inCapa = Set.singleton InputC

outCapa = Set.singleton OutputC

checkJudgements :: Set VarID -> Set NormalizedConstraint -> Constraint -> Bool
checkJudgements vphi = constraintsInclude

joinIndexVariables :: Set VarID -> Set VarID -> Set VarID
joinIndexVariables = Set.union -- for the multivariate implementation
--joinIndexVariables _ vphi = vphi -- for the univariate implementation (union for the multivariate case)

advance :: Set VarID -> Set NormalizedConstraint -> NormalizedIndex -> SType -> Maybe SType
advance _ _ _ t@(BaseST _) = Just t
advance vphi phi ixI (ChST ixJ ts sigma) | checkJudgement vphi phi (NormalizedConstraint (ixI .-. ixJ)) = Just $ ChST (ixJ .-. ixI) ts sigma
advance vphi phi ixI (ServST ixJ is k ts sigma)
  | checkJudgement vphi phi (NormalizedConstraint (ixI .-. ixJ)) = Just $ ServST (ixJ .-. ixI) is k ts sigma
  | otherwise = Just $ ServST (ixJ .-. ixI) is k ts (sigma `Set.intersection` Set.singleton OutputC)
advance _ _ _ _ = Nothing

advanceContext :: Set VarID -> Set NormalizedConstraint -> NormalizedIndex -> Context -> Maybe Context
advanceContext vphi phi ix g = sequence (Map.map (advance vphi phi ix) g)

defaultBaseType = NatBT zeroIndex zeroIndex

ready :: Set VarID -> Set NormalizedConstraint -> Context -> Context
ready vphi phi = Map.foldrWithKey filterMap Map.empty
  where
    filterMap v t@(BaseST _) gamma = Map.insert v t gamma
    filterMap v (ServST ixI is k ts sigma) gamma
      | checkJudgement vphi phi (NormalizedConstraint ixI) =
        Map.insert v (ServST ixI is k ts (sigma `Set.intersection` Set.singleton OutputC)) gamma
    filterMap _ _ gamma = gamma

isSubBaseType :: Set VarID -> Set NormalizedConstraint -> BType -> BType -> Bool
-- (SS-nweak)
isSubBaseType vphi phi (NatBT ixI ixJ) (NatBT ixI' ixJ') =
  checkJudgement vphi phi (NormalizedConstraint (ixI' .-. ixI))
    && checkJudgement vphi phi (NormalizedConstraint (ixJ .-. ixJ'))
-- (SS-lweak)
isSubBaseType vphi phi (ListBT ixI ixJ bt) (ListBT ixI' ixJ' bt') =
  checkJudgement vphi phi (NormalizedConstraint (ixI' .-. ixI))
    && checkJudgement vphi phi (NormalizedConstraint (ixJ .-. ixJ'))
    && isSubBaseType vphi phi bt bt'
isSubBaseType _ _ _ _ = False

isSubTypeList :: Set VarID -> Set NormalizedConstraint -> [SType] -> [SType] -> Bool
isSubTypeList vphi phi ts ts' =
  length ts == length ts'
    && Prelude.foldr (\(t', t) b -> b && isSubType vphi phi t' t) True (Prelude.zip ts' ts)

isSubType :: Set VarID -> Set NormalizedConstraint -> SType -> SType -> Bool
isSubType vphi phi (ServST ixI is ixK ts sigma) (ServST ixJ js ixK' ts' sigma')
  -- (SS-sinvar)
  | ixI == ixJ && is == js && sigma == sigma' && sigma' == inOutCapa =
    isSubTypeList vphi' phi ts ts'
      && isSubTypeList vphi' phi ts' ts
      && checkJudgement vphi' phi (NormalizedConstraint (ixK .-. ixK'))
      && checkJudgement vphi' phi (NormalizedConstraint (ixK' .-. ixK))
  -- (SS-scovar)
  | ixI == ixJ && is == js && sigma == sigma' && sigma' == inCapa =
    isSubTypeList vphi' phi ts ts'
      && checkJudgement vphi' phi (NormalizedConstraint (ixK' .-. ixK))
  -- (SS-scontra)
  | ixI == ixJ && is == js && sigma == sigma' && sigma' == outCapa =
    isSubTypeList vphi' phi ts' ts
      && checkJudgement vphi' phi (NormalizedConstraint (ixK .-. ixK'))
  -- (SS-srelax)
  | ixI == ixJ && is == js =
    (sigma' `isSubsetOf` sigma)
      && isSubType vphi phi (ServST ixI is ixK ts sigma') (ServST ixJ js ixK' ts' sigma')
  where
    vphi' = joinIndexVariables vphi $ Set.fromList is
isSubType vphi phi (ChST ixI ts sigma) (ChST ixJ ts' sigma')
  -- (SS-cinvar)
  | ixI == ixJ && sigma == sigma' && sigma' == inOutCapa =
    isSubTypeList vphi phi ts ts'
      && isSubTypeList vphi phi ts' ts
  -- (SS-ccovar)
  | ixI == ixJ && sigma == sigma' && sigma' == inCapa =
    isSubTypeList vphi phi ts ts'
  -- (SS-ccontra)
  | ixI == ixJ && sigma == sigma' && sigma' == outCapa =
    isSubTypeList vphi phi ts' ts
  -- (SS-crelax)
  | ixI == ixJ =
    (sigma' `isSubsetOf` sigma)
      && isSubType vphi phi (ChST ixI ts sigma') (ChST ixJ ts' sigma')
isSubType _ _ _ _ = False

-- Pair-wise sub-type checking
isSubTypes :: Set VarID -> Set NormalizedConstraint -> [SType] -> [SType] -> Bool
isSubTypes vphi phi t1s t2s = Prelude.foldr (\(t1, t2) res -> res && isSubType vphi phi t1 t2) True (zip t1s t2s)

checkExp :: Set VarID -> Set NormalizedConstraint -> Map Var SType -> Exp -> Maybe SType
-- (S-ZERO)
checkExp _ _ _ ZeroE = Just $ BaseST (NatBT zeroIndex zeroIndex)
--
-- (S-SUCC)
checkExp vphi phi gamma (SuccE e) = do
  (BaseST (NatBT ixI ixJ)) <- checkExp vphi phi gamma e
  return $ BaseST (NatBT (ixI .+. oneIndex) (ixJ .+. oneIndex))
--
-- (S-VAR)
checkExp _ _ gamma (VarE v) = Map.lookup v gamma
--
-- (S-EMPTY)
checkExp _ _ _ (ListE []) = Just $ BaseST (ListBT zeroIndex zeroIndex defaultBaseType)
--
-- (S-CONS)
checkExp vphi phi gamma (ListE (e : e')) = do
  (BaseST b) <- checkExp vphi phi gamma e
  (BaseST (ListBT ixI ixJ b')) <- checkExp vphi phi gamma (ListE e')
  if equalsConstant ixI 1 && equalsConstant ixJ 1
    then -- (S-CONS-2)
      return $ BaseST (ListBT oneIndex oneIndex b)
    else -- (S-CONS-1)

      if isSubBaseType vphi phi b' b
        then return $ BaseST (ListBT (ixI .+. oneIndex) (ixJ .+. oneIndex) b)
        else Nothing

checkExps :: Set VarID -> Set NormalizedConstraint -> Map Var SType -> [Exp] -> Maybe [SType]
checkExps vphi phi gamma = mapM (checkExp vphi phi gamma)

hasCapability :: IOCapability -> Var -> Context -> Bool
hasCapability c a gamma =
  case Map.lookup a gamma of
    Just (ChST _ _ cap) | Set.member c cap -> True
    Just (ServST _ _ _ _ cap) | Set.member c cap -> True
    _ -> False

hasInputCapability = hasCapability InputC

hasOutputCapability = hasCapability OutputC

isServer :: Context -> Var -> Bool
isServer gamma a =
  case Map.lookup a gamma of
    Just ServST {} -> True
    _ -> False

checkProc :: Set VarID -> Set NormalizedConstraint -> Map Var SType -> Proc -> Maybe NormalizedIndex
-- (S-nil)
checkProc _ _ _ NilP = Just zeroIndex
--
-- (S-tick)
checkProc vphi phi gamma (TickP p) = do
  gammaA <- advanceContext vphi phi oneIndex gamma
  k <- checkProc vphi phi gammaA p
  return $ k .+. oneIndex
--
-- (S-nu)
checkProc vphi phi gamma (RestrictP v t p) = checkProc vphi phi (Map.insert v t gamma) p
--
-- (S-ich)
checkProc vphi phi gamma (InputP a vs p) | hasInputCapability a gamma = do
  (ChST ixI ts cap) <- Map.lookup a gamma
  gammaA <- advanceContext vphi phi ixI gamma
  let gammaA' = gammaA `Map.union` Map.singleton a (ChST zeroIndex ts cap) `Map.union` Map.fromList (zip vs ts)
  k <- checkProc vphi phi gammaA' p
  return $ k .+. ixI
--
-- (S-och)
checkProc vphi phi gamma (OutputP a es subst) | hasOutputCapability a gamma && not (isServer gamma a) = do
  (ChST ixI ss cap) <- Map.lookup a gamma
  gammaA <- advanceContext vphi phi ixI gamma
  ts <- checkExps vphi phi gamma es
  if isSubTypes vphi phi ts ss
    then return ixI
    else Nothing
--
-- (S-oserv)
checkProc vphi phi gamma (OutputP a es subst) | hasOutputCapability a gamma && isServer gamma a = do
  (ServST ixI is k ss cap) <- Map.lookup a gamma
  gammaA <- advanceContext vphi phi ixI gamma
  ts <- checkExps vphi phi gamma es
  if isSubTypes vphi phi ts (Prelude.map (`SType.substituteVars` subst) ss)
    then return $ Index.substituteVars k subst
    else Nothing
--
-- (S-iserv)
checkProc vphi phi gamma (RepInputP a vs p) | hasInputCapability a gamma = do
  (ServST ixI is k ts cap) <- Map.lookup a gamma
  gammaA <- advanceContext vphi phi ixI gamma
  let gammaAR = ready vphi phi gammaA
  let gammaAR' = gammaAR `Map.union` Map.singleton a (ServST zeroIndex is k ts outCapa) `Map.union` Map.fromList (zip vs ts)
  k' <- checkProc vphi phi gammaAR' p
  if checkJudgements (vphi `joinIndexVariables` Set.fromList is) phi (k' :<=: k)
    then return ixI
    else Nothing
--
-- (S-par-1) + (S-par-2)
checkProc vphi phi gamma (p :|: q) = do
  k <- checkProc vphi phi gamma p
  k' <- checkProc vphi phi gamma q
  if checkJudgements vphi phi (k :<=: k')
    then return k'
    else return k
--
-- (S-nmatch-1) + (S-nmatch-2)
checkProc vphi phi gamma (MatchNatP e p x q) = do
  BaseST (NatBT ixI ixJ) <- checkExp vphi phi gamma e
  k <- checkProc vphi (phi `Set.union` normalizeConstraint (ixI :<=: zeroIndex)) gamma p
  k' <- checkProc vphi (phi `Set.union` normalizeConstraint (ixJ :>=: oneIndex)) (gamma `Map.union` Map.singleton x (BaseST (NatBT (ixI .-. oneIndex) (ixJ .-. oneIndex)))) q
  if checkJudgements vphi phi (k :<=: k')
    then return k'
    else return k
--
-- (S-lmatch-1) + (S-lmatch-2)
checkProc vphi phi gamma (MatchListP e p x y q) = do
  BaseST (ListBT ixI ixJ b) <- checkExp vphi phi gamma e
  k <- checkProc vphi (phi `Set.union` normalizeConstraint (ixI :<=: zeroIndex)) gamma p
  k' <- checkProc vphi (phi `Set.union` normalizeConstraint (ixJ :>=: oneIndex)) (gamma `Map.union` Map.fromList [(x, BaseST b), (y, BaseST (ListBT (ixI .-. oneIndex) (ixJ .-. oneIndex) b))]) q
  if checkJudgements vphi phi (k :<=: k')
    then return k'
    else return k
checkProc _ _ _ _ = Nothing