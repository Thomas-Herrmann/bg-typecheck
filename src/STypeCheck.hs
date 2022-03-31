{-# LANGUAGE FlexibleInstances #-}

module STypeCheck
  ( checkProcess,
  )
where

import Constraint (Constraint (..), NormalizedConstraint (..))
import ConstraintInclusion (constraintsInclude)
import Control.Monad.Except
import Control.Monad.State.Lazy
import qualified Data.Functor
import Data.Map as Map
import Data.Set as Set
import Index (NormalizedIndex, Subst, VarID, equalsConstant, evaluate, oneIndex, substituteVars, zeroIndex, (.*.), (.+.), (.-.), (./.))
import Normalization (normalizeConstraint, normalizeIndex)
import PiCalculus (Exp (..), Proc (..), Var)
import SType (BType (..), IOCapability (..), SType (..), substituteVars)

newtype CheckState = CheckState
  { stack :: [String]
  }

type Check a = StateT CheckState (Either (CheckState, String)) a

instance MonadFail (Either (CheckState, String)) where
  fail s = Left (CheckState [], s)

failWith :: Maybe a -> String -> Check a
failWith (Just val) msg = return val
failWith Nothing msg = do
  s <- get
  throwError (s, msg)

returnError :: String -> Check a
returnError msg = do
  s <- get
  throwError (s, msg)

inContext :: String -> Check a -> Check a
inContext s action = do
  modify $ \st -> st {stack = s : stack st}
  res <- action
  modify $ \st -> st {stack = tail $ stack st}
  return res

type Context = Map Var SType

inOutCapa = Set.fromList [InputC, OutputC]

inCapa = Set.singleton InputC

outCapa = Set.singleton OutputC

checkJudgements :: Set VarID -> Set NormalizedConstraint -> Constraint -> Bool
checkJudgements vphi = constraintsInclude

joinIndexVariables :: Set VarID -> Set VarID -> Set VarID
joinIndexVariables = Set.union -- for the multivariate implementation
--joinIndexVariables _ vphi = vphi -- for the univariate implementation (union for the multivariate case)

advance :: Set VarID -> Set NormalizedConstraint -> NormalizedIndex -> SType -> Check SType
advance _ _ _ t@(BaseST _) = return t
advance vphi phi ixI (ChST ixJ ts sigma)
  | checkJudgements vphi phi (ixJ :>=: ixI) = return $ ChST (ixJ .-. ixI) ts sigma
  | otherwise = returnError "Failed to advance"
advance vphi phi ixI (ServST ixJ is k ts sigma)
  | checkJudgements vphi phi (ixJ :>=: ixI) = return $ ServST (ixJ .-. ixI) is k ts sigma
  | otherwise = return $ ServST (ixJ .-. ixI) is k ts (sigma `Set.intersection` Set.singleton OutputC)

advanceContext :: Set VarID -> Set NormalizedConstraint -> NormalizedIndex -> Context -> Check Context
advanceContext vphi phi ix g = sequence (Map.map (advance vphi phi ix) g)

defaultBaseType = NatBT zeroIndex zeroIndex

ready :: Set VarID -> Set NormalizedConstraint -> Context -> Context
ready vphi phi = Map.foldrWithKey filterMap Map.empty
  where
    filterMap v t@(BaseST _) gamma = Map.insert v t gamma
    filterMap v (ServST ixI is k ts sigma) gamma
      | checkJudgements vphi phi (ixI :<=: zeroIndex) =
        Map.insert v (ServST ixI is k ts (sigma `Set.intersection` Set.singleton OutputC)) gamma
    filterMap _ _ gamma = gamma

isSubTypeList :: Set VarID -> Set NormalizedConstraint -> [SType] -> [SType] -> Bool
isSubTypeList vphi phi ts ts' =
  length ts == length ts'
    && Prelude.foldr (\(t', t) b -> b && isSubType vphi phi t' t) True (Prelude.zip ts' ts)

baseJoin :: Set VarID -> Set NormalizedConstraint -> BType -> BType -> Check BType
baseJoin vphi phi (NatBT ixI ixJ) (NatBT ixI' ixJ')
  | constraintsInclude phi (ixI :<=: ixI') && constraintsInclude phi (ixJ' :<=: ixJ) = return (NatBT ixI ixJ)
  | constraintsInclude phi (ixI' :<=: ixI) && constraintsInclude phi (ixJ' :<=: ixJ) = return (NatBT ixI' ixJ)
  | constraintsInclude phi (ixI :<=: ixI') && constraintsInclude phi (ixJ :<=: ixJ') = return (NatBT ixI ixJ')
  | constraintsInclude phi (ixI' :<=: ixI) && constraintsInclude phi (ixJ :<=: ixJ') = return (NatBT ixI' ixJ')
baseJoin vphi phi (ListBT ixI ixJ b) (ListBT ixI' ixJ' b')
  | constraintsInclude phi (ixI :<=: ixI') && constraintsInclude phi (ixJ' :<=: ixJ) = baseJoin vphi phi b b' Data.Functor.<&> ListBT ixI ixJ
  | constraintsInclude phi (ixI' :<=: ixI) && constraintsInclude phi (ixJ' :<=: ixJ) = baseJoin vphi phi b b' Data.Functor.<&> ListBT ixI' ixJ
  | constraintsInclude phi (ixI :<=: ixI') && constraintsInclude phi (ixJ :<=: ixJ') = baseJoin vphi phi b b' Data.Functor.<&> ListBT ixI ixJ
  | constraintsInclude phi (ixI' :<=: ixI) && constraintsInclude phi (ixJ :<=: ixJ') = baseJoin vphi phi b b' Data.Functor.<&> ListBT ixI' ixJ
baseJoin _ _ _ _ = returnError "baseJoin fail"

instantiate :: [VarID] -> [SType] -> Check Subst
instantiate vars types = inContext "instantiate" $ do
  res <- instantiate' vars types
  case res of
    ([], s) -> return s
    res -> returnError $ "instantiate fail " ++ "vars = " ++ show vars ++ ", types = " ++ show types ++ ", (restVar, subst) = " ++ show res

instantiate' :: [VarID] -> [SType] -> Check ([VarID], Subst)
instantiate' vars [] = return (vars, Map.empty)
instantiate' vars (t : ts) = do
  (r, s) <- instantiateSingle vars t
  (r, s') <- instantiate' r ts
  return (r, s `Map.union` s')

instantiateSingle :: [VarID] -> SType -> Check ([VarID], Subst)
instantiateSingle (i : j : k) (BaseST (NatBT ixI ixJ)) = do
  return (k, Map.fromList [(i, ixI), (j, ixJ)])
instantiateSingle (i : j : k) (BaseST (ListBT ixI ixJ b)) = do
  (r, s) <- instantiateSingle k (BaseST b)
  return (r, s `Map.union` Map.fromList [(i, ixI), (j, ixJ)])
instantiateSingle (i : j) (ChST ixI ts sigma) = do
  (r, s) <- instantiate' j ts
  return (r, s `Map.union` Map.singleton i ixI)
instantiateSingle (i : j : k) (ServST ixI _ kc ts sigma) = do
  (r, s) <- instantiate' k ts
  return (r, s `Map.union` Map.fromList [(i, ixI), (j, kc)])
instantiateSingle vars typ = returnError $ "instantiateSingle fail: " ++ "vars = " ++ show vars ++ ", typ = " ++ show typ

isSubBaseType :: Set VarID -> Set NormalizedConstraint -> BType -> BType -> Bool
-- (SS-nweak)
isSubBaseType vphi phi (NatBT ixI ixJ) (NatBT ixI' ixJ') =
  checkJudgements vphi phi (ixI' :<=: ixI)
    && checkJudgements vphi phi (ixJ :<=: ixJ')
-- (SS-lweak)
isSubBaseType vphi phi (ListBT ixI ixJ bt) (ListBT ixI' ixJ' bt') =
  checkJudgements vphi phi (ixI' :<=: ixI)
    && checkJudgements vphi phi (ixJ :<=: ixJ')
    && isSubBaseType vphi phi bt bt'
isSubBaseType _ _ _ _ = False

isSubType :: Set VarID -> Set NormalizedConstraint -> SType -> SType -> Bool
isSubType vphi phi (BaseST b) (BaseST b') = isSubBaseType vphi phi b b'
isSubType vphi phi (ServST ixI is ixK ts sigma) (ServST ixJ js ixK' ts' sigma')
  -- (SS-sinvar)
  | ixI == ixJ && is == js && sigma == sigma' && sigma' == inOutCapa =
    isSubTypeList vphi' phi ts ts'
      && isSubTypeList vphi' phi ts' ts
      && checkJudgements vphi' phi (ixK :=: ixK')
  -- (SS-scovar)
  | ixI == ixJ && is == js && sigma == sigma' && sigma' == inCapa =
    isSubTypeList vphi' phi ts ts'
      && checkJudgements vphi' phi (ixK' :<=: ixK)
  -- (SS-scontra)
  | ixI == ixJ && is == js && sigma == sigma' && sigma' == outCapa =
    isSubTypeList vphi' phi ts' ts
      && checkJudgements vphi' phi (ixK :<=: ixK')
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

checkExp :: Set VarID -> Set NormalizedConstraint -> Map Var SType -> Exp -> Check SType
-- (S-zero)
checkExp _ _ _ ZeroE = inContext "(S-zero)" $ return $ BaseST (NatBT zeroIndex zeroIndex)
--
-- (S-succ)
checkExp vphi phi gamma (SuccE e) = inContext "(S-succ)" $ do
  (BaseST (NatBT ixI ixJ)) <- checkExp vphi phi gamma e
  return $ BaseST (NatBT (ixI .+. oneIndex) (ixJ .+. oneIndex))
--
-- (S-var)
checkExp _ _ gamma (VarE v) = inContext "(S-var)" $ Map.lookup v gamma `failWith` "unbound variable"
--
-- (S-empty)
checkExp _ _ _ (ListE []) = inContext "(S-empty)" $ return $ BaseST (ListBT zeroIndex zeroIndex defaultBaseType)
--
-- (S-cons)
checkExp vphi phi gamma (ListE (e : e')) = inContext "(S-cons)" $ do
  (BaseST b) <- checkExp vphi phi gamma e
  (BaseST (ListBT ixI ixJ b')) <- checkExp vphi phi gamma (ListE e')
  bJoined <- baseJoin vphi phi b b'
  return $ BaseST (ListBT (ixI .+. oneIndex) (ixJ .+. oneIndex) bJoined)

checkExps :: Set VarID -> Set NormalizedConstraint -> Map Var SType -> [Exp] -> Check [SType]
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

checkProc :: Set VarID -> Set NormalizedConstraint -> Map Var SType -> Proc -> Check NormalizedIndex
-- (S-nil)
checkProc _ _ _ NilP = return zeroIndex
--
-- (S-tick)
checkProc vphi phi gamma (TickP p) = inContext "(S-tick)" $ do
  gammaA <- advanceContext vphi phi oneIndex gamma
  k <- checkProc vphi phi gammaA p
  return $ k .+. oneIndex
--
-- (S-nu)
checkProc vphi phi gamma (RestrictP v t p) = inContext "(S-nu)" $ checkProc vphi phi (Map.insert v t gamma) p
--
-- (S-ich)
checkProc vphi phi gamma (InputP a vs p) | hasInputCapability a gamma = inContext "(S-ich)" $ do
  (ChST ixI ts cap) <- Map.lookup a gamma `failWith` "unbound variable"
  gammaA <- advanceContext vphi phi ixI gamma
  let gammaA' = gammaA `Map.union` Map.singleton a (ChST zeroIndex ts cap) `Map.union` Map.fromList (zip vs ts)
  k <- checkProc vphi phi gammaA' p
  return $ k .+. ixI
--
-- (S-och)
checkProc vphi phi gamma (OutputP a es) | hasOutputCapability a gamma && not (isServer gamma a) = inContext "(S-och)" $ do
  (ChST ixI ss cap) <- Map.lookup a gamma `failWith` "unbound variable"
  gammaA <- advanceContext vphi phi ixI gamma
  ts <- checkExps vphi phi gamma es
  if isSubTypes vphi phi ts ss
    then return ixI
    else returnError $ "(S-och) fail ~T <= ~S where " ++ "~T = " ++ show ts ++ ", ~S = " ++ show ss ++ ", phi = " ++ show phi
--
-- (S-oserv)
checkProc vphi phi gamma (OutputP a es) | hasOutputCapability a gamma && isServer gamma a = inContext "(S-oserv)" $ do
  (ServST ixI is k ss cap) <- Map.lookup a gamma `failWith` "unbound variable"
  gammaA <- advanceContext vphi phi ixI gamma
  ts <- checkExps vphi phi gamma es
  subst <- instantiate is ts
  if isSubTypes vphi phi ts (Prelude.map (`SType.substituteVars` subst) ss)
    then return $ Index.substituteVars k subst
    else returnError $ "~T <= ~S where " ++ "~T = " ++ show ts ++ ", ~S = " ++ show ss ++ ", phi = " ++ show phi
--
-- (S-iserv)
checkProc vphi phi gamma (RepInputP a vs p) | hasInputCapability a gamma = inContext "(S-iserv)" $ do
  (ServST ixI is k ts cap) <- Map.lookup a gamma `failWith` "unbound variable"
  gammaA <- advanceContext vphi phi ixI gamma
  let gammaAR = ready vphi phi gammaA
  let gammaAR' = gammaAR `Map.union` Map.singleton a (ServST zeroIndex is k ts outCapa) `Map.union` Map.fromList (zip vs ts)
  k' <- checkProc vphi phi gammaAR' p
  if checkJudgements (vphi `joinIndexVariables` Set.fromList is) phi (k' :<=: k)
    then return ixI
    else returnError "Judgement failed"
--
-- (S-par)
checkProc vphi phi gamma (p :|: q) = inContext "(S-par)" $ do
  k <- checkProc vphi phi gamma p
  k' <- checkProc vphi phi gamma q
  let l
        | checkJudgements vphi phi (k :<=: k') = k
        | checkJudgements vphi phi (k :<=: k') = k'
        | otherwise = k .+. k'
  return l
--
-- (S-nmatch)
checkProc vphi phi gamma (MatchNatP e p x q) = inContext "(S-nmatch)" $ do
  BaseST (NatBT ixI ixJ) <- checkExp vphi phi gamma e
  k <- checkProc vphi (phi `Set.union` normalizeConstraint (ixI :<=: zeroIndex)) gamma p
  k' <- checkProc vphi (phi `Set.union` normalizeConstraint (ixJ :>=: oneIndex)) (gamma `Map.union` Map.singleton x (BaseST (NatBT (ixI .-. oneIndex) (ixJ .-. oneIndex)))) q
  let l
        | checkJudgements vphi phi (k :<=: k') = k
        | checkJudgements vphi phi (k :<=: k') = k'
        | otherwise = k .+. k'
  return l
--
-- (S-lmatch)
checkProc vphi phi gamma (MatchListP e p x y q) = inContext "(S-lmatch)" $ do
  BaseST (ListBT ixI ixJ b) <- checkExp vphi phi gamma e
  k <- checkProc vphi (phi `Set.union` normalizeConstraint (ixI :<=: zeroIndex)) gamma p
  k' <- checkProc vphi (phi `Set.union` normalizeConstraint (ixJ :>=: oneIndex)) (gamma `Map.union` Map.fromList [(x, BaseST b), (y, BaseST (ListBT (ixI .-. oneIndex) (ixJ .-. oneIndex) b))]) q
  let l
        | checkJudgements vphi phi (k :<=: k') = k
        | checkJudgements vphi phi (k :<=: k') = k'
        | otherwise = k .+. k'
  return l
checkProc _ _ _ _ = inContext "invalid process" $ returnError "Unhandled process fail"

checkProcess :: Set VarID -> Set NormalizedConstraint -> Map Var SType -> Proc -> Either String NormalizedIndex
checkProcess vphi phi gamma p =
  case evalStateT (checkProc vphi phi gamma p) (CheckState {stack = []}) of
    Left (CheckState s, msg) -> Left $ "Error during process check: " ++ msg ++ "\nStackTrace: " ++ show s
    Right k -> Right k