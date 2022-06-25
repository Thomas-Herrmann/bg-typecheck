{-# LANGUAGE FlexibleInstances #-}

module STypeCheck
  ( checkProcess,
  )
where

import Constraint (Constraint (..), NormalizedConstraint (..))
import ConstraintInclusion (constraintsIncludeZ3)
import Control.Monad.Trans.Except
import Control.Monad.State.Lazy
import qualified Data.Functor
import Data.Map as Map
import Data.Set as Set
import Index (NormalizedIndex, Subst, VarID, equalsConstant, evaluate, oneIndex, substituteVars, zeroIndex, (.*.), (.+.), (.-.), (./.))
import Normalization (normalizeConstraint, normalizeIndex)
import PiCalculus (Exp (..), Proc (..), Var)
import SType (IOCapability (..), SType (..), substituteVars)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Extra (ifM, unlessM)

newtype CheckState = CheckState
  { stack :: [(String, [(String, String)])]
  }

type Check a = ExceptT (CheckState, String) (StateT CheckState IO) a


failWith :: Maybe a -> String -> Check a
failWith (Just val) msg = return val
failWith Nothing msg = do
  s <- get
  throwE (s, msg)

returnError :: String -> Check a
returnError msg = do
  s <- get
  throwE (s, msg)

inContext :: String -> [(String, String)] -> Check a -> Check a
inContext name bindings action = do
  modify $ \st -> st {stack = (name, bindings) : stack st}
  res <- action
  modify $ \st -> st {stack = tail $ stack st}
  return res

type Context = Map Var SType

inOutCapa = Set.fromList [InputC, OutputC]

inCapa = Set.singleton InputC

outCapa = Set.singleton OutputC

checkJudgements :: Set VarID -> Set NormalizedConstraint -> Constraint -> Check Bool
checkJudgements vphi phi c = liftIO $ constraintsIncludeZ3 phi c -- todo use vphi ..

joinIndexVariables :: Set VarID -> Set VarID -> Set VarID
joinIndexVariables = Set.union -- for the multivariate implementation
--joinIndexVariables _ vphi = vphi -- for the univariate implementation (union for the multivariate case)

advance :: Set VarID -> Set NormalizedConstraint -> NormalizedIndex -> SType -> Check SType
advance _ _ _ t@(NatST _ _) = return t
advance vphi phi ixI (ChST ixJ ts sigma) =
  ifM (checkJudgements vphi phi (ixJ :>=: ixI))
    (return $ ChST (ixJ .-. ixI) ts sigma)
    (return $ ChST zeroIndex ts Set.empty)

advance vphi phi ixI (ServST ixJ is k ts sigma) =
  ifM (checkJudgements vphi phi (ixJ :>=: ixI))
    (return $ ServST (ixJ .-. ixI) is k ts sigma)
    (ifM (checkJudgements vphi phi (ixI :>=: ixJ))
      (safeIndexSubtraction vphi phi ixI ixJ >>= (\ix' -> return $ ServST ix' is k ts (sigma `Set.intersection` Set.singleton OutputC)))
      (return $ LockedServST ixJ is k ts sigma ixI))

advance vphi phi ixI (LockedServST ixJ is k ts sigma ixL) =
  ifM (checkJudgements vphi phi ((ixL .+. ixI) :>=: ixJ))
    (return $ ServST zeroIndex is k ts sigma)
    (return $ LockedServST ixJ is k ts sigma (ixL .+. ixI))


advanceContext :: Set VarID -> Set NormalizedConstraint -> NormalizedIndex -> Context -> Check Context
advanceContext vphi phi ix g = sequence (Map.map (advance vphi phi ix) g)


ready :: Set VarID -> Set NormalizedConstraint -> Context -> Check Context
ready vphi phi = Map.foldrWithKey filterMap (return Map.empty)
  where
    filterMap v t@(NatST _ _) mgamma = mgamma >>= (\gamma -> return $ Map.insert v t gamma)
    filterMap v (ServST ixI is k ts sigma) mgamma = do
      gamma <- mgamma
      ifM (checkJudgements vphi phi (ixI :<=: zeroIndex))
        (return $ Map.insert v (ServST ixI is k ts (sigma `Set.intersection` Set.singleton OutputC)) gamma)
        (return $ gamma)

    filterMap _ _ mgamma = mgamma

isSubTypeList :: Set VarID -> Set NormalizedConstraint -> [SType] -> [SType] -> Check Bool
isSubTypeList vphi phi ts ts' =
  if length ts == length ts'
    then foldM (\b (t', t) -> isSubType vphi phi t' t >>= (\b' -> return $ b && b')) True (Prelude.zip ts' ts)
    else return False

instantiate :: [VarID] -> [SType] -> Check Subst
instantiate vars types =
  inContext "instantiate" [("vars", show vars), ("types", show types)] $ do
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
instantiateSingle (i : j : k) (NatST ixI ixJ) = return (k, Map.fromList [(i, ixI), (j, ixJ)])
instantiateSingle (i : j) (ChST ixI ts sigma) = do
  (r, s) <- instantiate' j ts
  return (r, s `Map.union` Map.singleton i ixI)
instantiateSingle (i : j : k) (ServST ixI _ kc ts sigma) = do
  (r, s) <- instantiate' k ts
  return (r, s `Map.union` Map.fromList [(i, ixI), (j, kc)])
instantiateSingle vars typ = returnError $ "instantiateSingle fail: " ++ "vars = " ++ show vars ++ ", typ = " ++ show typ


isSubType :: Set VarID -> Set NormalizedConstraint -> SType -> SType -> Check Bool
isSubType vphi phi (NatST ixI ixJ) (NatST ixI' ixJ') = do
   b <- checkJudgements vphi phi (ixI' :<=: ixI)
   b' <- checkJudgements vphi phi (ixJ :<=: ixJ')
   return $ b && b'

isSubType vphi phi (ServST ixI is ixK ts sigma) (ServST ixJ js ixK' ts' sigma')
  -- (SS-sinvar)
  | ixI == ixJ && is == js && sigma == sigma' && sigma' == inOutCapa = do
    b <- isSubTypeList vphi' phi ts ts'
    b' <- isSubTypeList vphi' phi ts' ts
    b'' <- checkJudgements vphi' phi (ixK :=: ixK')
    return $ b && b' && b''

  -- (SS-scovar)
  | ixI == ixJ && is == js && inCapa `Set.isSubsetOf` sigma && sigma' == inCapa = do
    b <- isSubTypeList vphi' phi ts ts'
    b' <- checkJudgements vphi' phi (ixK' :<=: ixK)
    return $ b && b'

  -- (SS-scontra)
  | ixI == ixJ && is == js && outCapa `Set.isSubsetOf` sigma && sigma' == outCapa = do
    b <- isSubTypeList vphi' phi ts' ts
    b' <- checkJudgements vphi' phi (ixK :<=: ixK')
    return $ b && b'

  -- (SS-srelax)
  | ixI == ixJ && is == js = do
    b <- isSubType vphi phi (ServST ixI is ixK ts sigma') (ServST ixJ js ixK' ts' sigma')
    return $ b && (sigma' `isSubsetOf` sigma)
  where
    vphi' = joinIndexVariables vphi $ Set.fromList is

isSubType vphi phi (ChST ixI ts sigma) (ChST ixJ ts' sigma')
  -- (SS-cinvar)
  | ixI == ixJ && sigma == sigma' && sigma' == inOutCapa = do
    b <- isSubTypeList vphi phi ts ts'
    b' <- isSubTypeList vphi phi ts' ts
    return $ b && b'

  -- (SS-ccovar)
  | ixI == ixJ && inCapa `Set.isSubsetOf` sigma && sigma' == inCapa = isSubTypeList vphi phi ts ts'
  -- (SS-ccontra)
  | ixI == ixJ && outCapa `Set.isSubsetOf` sigma && sigma' == outCapa = isSubTypeList vphi phi ts' ts
  -- (SS-crelax)
  | ixI == ixJ = do
    b <- isSubType vphi phi (ChST ixI ts sigma') (ChST ixJ ts' sigma')
    return $ b && (sigma' `isSubsetOf` sigma)
    
isSubType _ _ _ _ = return False

-- Pair-wise sub-type checking
isSubTypes :: Set VarID -> Set NormalizedConstraint -> [SType] -> [SType] -> Check Bool
isSubTypes vphi phi t1s t2s = foldM (\b (t1, t2) -> isSubType vphi phi t1 t2 >>= (\b' -> return $ b && b')) True (zip t1s t2s)

checkSubType :: Set VarID -> Set NormalizedConstraint -> SType -> SType -> Check ()
checkSubType vphi phi t1 t2 =
  unlessM (isSubType vphi phi t1 t2) $
    inContext "checkSubType" [("T", show t1), ("S", show t2)] $
      returnError "Failed subtype check T <= S"

checkSubTypes :: Set VarID -> Set NormalizedConstraint -> [SType] -> [SType] -> Check ()
checkSubTypes vphi phi t1s t2s =
  inContext "checkSubTypes" [("~T", show t1s), ("~S", show t2s)] $
    foldM (\_ (t1, t2) -> checkSubType vphi phi t1 t2) () (zip t1s t2s)

checkExp :: Set VarID -> Set NormalizedConstraint -> Map Var SType -> Exp -> Check SType
-- (S-zero)
checkExp _ _ _ exp@ZeroE =
  inContext "(S-zero)" [("exp", show exp)] $
    return $ NatST zeroIndex zeroIndex
--
-- (S-succ)
checkExp vphi phi gamma exp@(SuccE e) =
  inContext "(S-succ)" [("exp", show exp)] $ do
    NatST ixI ixJ <- checkExp vphi phi gamma e
    return $ NatST (ixI .+. oneIndex) (ixJ .+. oneIndex)
--
-- (S-var)
checkExp _ _ gamma exp@(VarE v) =
  inContext "(S-var)" [("exp", show exp)] $
    Map.lookup v gamma `failWith` "unbound variable"


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

-- Safely subtracts two indices taking monus behavior into account
safeIndexSubtraction :: Set VarID -> Set NormalizedConstraint -> NormalizedIndex -> NormalizedIndex -> Check NormalizedIndex
safeIndexSubtraction vphi phi ixI ixJ =
  inContext "safeIndexSubtraction" [("ixI", show ixI), ("ixJ", show ixJ), ("phi", show phi)] $ do
    b <- checkJudgements vphi phi (ixI :>=: ixJ)
    b' <- checkJudgements vphi phi (ixI :<=: zeroIndex)
    case (b, b') of
      (True, _) -> return (ixI .-. ixJ)
      (_, True) -> return zeroIndex
      _ -> returnError "Failed index subtraction ixI - ixJ"

checkProc :: Set VarID -> Set NormalizedConstraint -> Map Var SType -> Proc -> Check NormalizedIndex
-- (S-nil)
checkProc _ _ _ NilP = return zeroIndex
--
-- (S-tick)
checkProc vphi phi gamma pro@(TickP p) =
  inContext "(S-tick)" [("process", show pro), ("vphi", show vphi), ("phi", show phi)] $ do
    gammaA <- advanceContext vphi phi oneIndex gamma
    k <- checkProc vphi phi gammaA p
    return $ k .+. oneIndex
--
-- (S-nu)
checkProc vphi phi gamma pro@(RestrictP v t p) =
  inContext "(S-nu)" [("process", show pro)] $
    checkProc vphi phi (Map.insert v t gamma) p
--
-- (S-ich)
checkProc vphi phi gamma pro@(InputP a vs p) | hasInputCapability a gamma =
  inContext "(S-ich)" [("process", show pro), ("vphi", show vphi), ("phi", show phi)] $ do
    (ChST ixI ts cap) <- Map.lookup a gamma `failWith` "unbound variable"
    gammaA <- advanceContext vphi phi ixI gamma
    let gammaA' = gammaA `Map.union` Map.singleton a (ChST zeroIndex ts cap) `Map.union` Map.fromList (zip vs ts)
    k <- checkProc vphi phi gammaA' p
    return $ k .+. ixI
--
-- (S-och)
checkProc vphi phi gamma pro@(OutputP a es) | hasOutputCapability a gamma && not (isServer gamma a) =
  inContext "(S-och)" [("process", show pro), ("vphi", show vphi), ("phi", show phi)] $ do
    (ChST ixI ss cap) <- Map.lookup a gamma `failWith` "unbound variable"
    gammaA <- advanceContext vphi phi ixI gamma
    ts <- checkExps vphi phi gamma es
    checkSubTypes vphi phi ts ss
    return ixI
--
-- (S-oserv)
checkProc vphi phi gamma pro@(OutputP a es) | hasOutputCapability a gamma && isServer gamma a =
  inContext "(S-oserv)" [("process", show pro), ("vphi", show vphi), ("phi", show phi)] $ do
    (ServST ixI is k ss cap) <- Map.lookup a gamma `failWith` "unbound variable"
    gammaA <- advanceContext vphi phi ixI gamma
    ts <- checkExps vphi phi gamma es
    subst <- instantiate is ts
    checkSubTypes vphi phi ts (Prelude.map (`SType.substituteVars` subst) ss)
    return $ Index.substituteVars k subst
--
-- (S-iserv)
checkProc vphi phi gamma pro@(RepInputP a vs p) | hasInputCapability a gamma =
  inContext "(S-iserv)" [("process", show pro), ("vphi", show vphi), ("phi", show phi)] $ do
    (ServST ixI is k ts cap) <- Map.lookup a gamma `failWith` "unbound variable"
    gammaA <- advanceContext vphi phi ixI gamma
    gammaAR <- ready vphi phi gammaA
    let gammaAR' = gammaAR `Map.union` Map.singleton a (ServST zeroIndex is k ts outCapa) `Map.union` Map.fromList (zip vs ts)
    k' <- checkProc vphi phi gammaAR' p
    ifM (checkJudgements (vphi `joinIndexVariables` Set.fromList is) phi (k' :<=: k))
      (return ixI)
      (returnError "Judgement failed")
--
-- (S-par)
checkProc vphi phi gamma pro@(p :|: q) =
  inContext "(S-par)" [("process", show pro), ("vphi", show vphi), ("phi", show phi)] $ do
    k <- checkProc vphi phi gamma p
    k' <- checkProc vphi phi gamma q
    kgreater <- checkJudgements vphi phi (k' :<=: k)
    ksmaller <- checkJudgements vphi phi (k :<=: k')
    let l
          | kgreater = k
          | ksmaller = k'
          | otherwise = k .+. k'
    return l
--
-- (S-nmatch)
checkProc vphi phi gamma pro@(MatchNatP e p x q) =
  inContext "(S-nmatch)" [("process", show pro), ("vphi", show vphi), ("phi", show phi)] $ do
    NatST ixI ixJ <- checkExp vphi phi gamma e
    k <- checkProc vphi (phi `Set.union` normalizeConstraint (ixI :<=: zeroIndex)) gamma p
    ixI' <- safeIndexSubtraction vphi (phi `Set.union` normalizeConstraint (ixJ :>=: oneIndex)) ixI oneIndex
    ixJ' <- safeIndexSubtraction vphi (phi `Set.union` normalizeConstraint (ixJ :>=: oneIndex)) ixJ oneIndex
    k' <- checkProc vphi (phi `Set.union` normalizeConstraint (ixJ :>=: oneIndex)) (gamma `Map.union` Map.singleton x (NatST ixI' ixJ')) q
    kgreater <- checkJudgements vphi phi (k' :<=: k)
    ksmaller <- checkJudgements vphi phi (k :<=: k')
    let l
          | kgreater = k
          | ksmaller = k'
          | otherwise = k .+. k'
    return l

checkProc _ _ _ pro = inContext "invalid process" [("process", show pro)] $ returnError "No valid type rule"

evalCheck :: Check a -> IO (Either String a)
evalCheck m = do
  m' <- evalStateT (runExceptT m) (CheckState {stack = []})
  case m' of
    Left (CheckState s, msg) -> return $
      Left 
        ("Error during process check: " ++ msg ++ "\n"
          ++ "StackTrace: "
          ++ show (Prelude.map fst s)
          ++ "\n"
          ++ "Relevant bindings: "
          ++ (if not (Prelude.null s) then (showBindings . snd . head) s else "Invalid")
          ++ "Relevant bindings 2: "
          ++ (if Prelude.length s >= 2 then (showBindings . snd . head . tail) s else "Invalid")
          ++ "Relevant bindings 3: "
          ++ (if Prelude.length s >= 3 then (showBindings . snd . head . tail . tail) s else "Invalid"))
    Right k -> return $ Right k
  where
    showBindings bindings = "\n" ++ Prelude.foldr (\(var, t) acc -> "  " ++ var ++ " : " ++ t ++ "\n" ++ acc) "" bindings

checkProcess :: Set VarID -> Set NormalizedConstraint -> Map Var SType -> Proc -> IO (Either String NormalizedIndex)
checkProcess vphi phi gamma p = evalCheck $ checkProc vphi phi gamma p