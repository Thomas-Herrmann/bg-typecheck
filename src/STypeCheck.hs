module STypeCheck
  (
  )
where

import Constraint (NormalizedConstraint (..), Constraint (..))
import Normalization (normalize, normalizeIndex)
import Index (NormalizedIndex, VarID, zeroIndex, oneIndex, (.+.), (.-.), (.*.), (./.))
import Intervals (checkJudgement)
import PiCalculus (Var, Exp(..), Proc(..))
import SType (SType (..))
import Data.Set as Set
import Data.Map as Map


type Context = Map Var SType

inOutCapa = Set.fromList [InputC, OutputC]

inCapa = Set.singleton InputC

outCapa = Set.singleton OutputC


joinIndexVariables :: Set VarID -> Set VarID -> Set VarID
joinIndexVariables _ vphi = vphi -- for the univariate implementation (union for the multivariate case)


advance :: Set VarID -> Set NormalizedConstraint -> NormalizedIndex -> SType -> Maybe SType
advance _ _ _ t@(BaseST _) = Just t
advance vphi phi ixI (ChST ixJ ts sigma) | checkJudgement vphi phi (NormalizedConstraint (ixI .-. ixJ)) = Just $ ChST (ixJ .-. ixI) ts sigma

advance vphi phi ixI (ServST ixJ is k ts sigma) 
  | checkJudgement vphi phi (NormalizedConstraint (ixI .-. ixJ)) = Just $ ServST (ixJ .-. ixI) is k ts sigma
  | otherwise = Just $ ServST (ixJ .-. ixI) is k ts (sigma `Set.intersection` Set.singleton OutputC)
                                  
advance _ _ _ = Nothing


ready :: Set VarID -> Set NormalizedConstraint -> Context -> Context
ready vphi phi = Map.foldrWithKey filterMap Map.empty
  where
    filterMap v t@(BaseST _) = Map.insert v t
    filterMap v (ServST ixI is k ts sigma) gamma | checkJudgement vphi phi (NormalizedConstraint ixI) = Map.insert v (ServST ixI is k ts (sigma `Set.intersection` Set.singleton OutputC)) gamma
    filterMap _ _ gamma = gamma


isSubBaseType :: Set VarID -> Set NormalizedConstraint -> BType -> BType -> Bool
-- (SS-nweak)
isSubBaseType vphi phi (NatBT ixI ixJ) (NatBT ixI' ixJ') = 
  checkJudgement vphi phi (NormalizedConstraint (ixI' .-. ixI)) && 
  checkJudgement vphi phi (NormalizedConstraint (ixJ .-. ixJ'))

-- (SS-lweak)
isSubBaseType vphi phi (ListBT ixI ixJ bt) (ListBT ixI' ixJ' bt') = 
  checkJudgement vphi phi (NormalizedConstraint (ixI' .-. ixI)) && 
  checkJudgement vphi phi (NormalizedConstraint (ixJ .-. ixJ')) &&
  isSubBaseType vphi phi bt bt'

isSubBaseType _ _ _ _ = False


isSubType :: Set VarID -> Set NormalizedConstraint -> SType -> SType -> Bool
isSubType vphi phi (ServST ixI is ixK ts sigma) (ServST ixJ js ixK' ts' sigma')
  -- (SS-sinvar)
  | ixI == ixJ && is == js && sigma == sigma' == inOutCapa = 
    isSubType vphi' phi ts ts' && 
    isSubType vphi' phi ts' ts && 
    checkJudgement vphi' phi (NormalizedConstraint (ixK .-. ixK')) && 
    checkJudgement vphi' phi (NormalizedConstraint (ixK' .-. ixK))
  
  -- (SS-scovar)
  | ixI == ixJ && is == js && sigma == sigma' == inCapa = 
    isSubType vphi' phi ts ts' && 
    checkJudgement vphi' phi (NormalizedConstraint (ixK' .-. ixK))

  -- (SS-scontra)
  | ixI == ixJ && is == js && sigma == sigma' == outCapa =
    isSubType vphi' phi ts' ts && 
    checkJudgement vphi' phi (NormalizedConstraint (ixK .-. ixK'))

  -- (SS-srelax)
  | ixI == ixJ && is == js = 
    (sigma' `isSubsetOf` sigma) && 
    isSubType vphi phi (ServST ixI is ixK ts sigma') (ServST ixJ js ixK' ts' sigma')
  where
    vphi' = joinIndexVariables vphi $ Set.fromList ixI


isSubType vphi phi (ChST ixI ts sigma) (ChST ixJ ts' sigma') 
  -- (SS-cinvar)
  | ixI == ixJ && sigma == sigma' == inOutCapa =
    isSubType vphi' phi ts ts' &&
    isSubType vphi' phi ts' ts

  -- (SS-ccovar)
  | ixI == ixJ && sigma == sigma' == inCapa =
    isSubType vphi' phi ts ts'
  
  -- (SS-ccontra)
  | ixI == ixJ && sigma == sigma' == outCapa =
    isSubType vphi' phi ts' ts

  -- (SS-crelax)
  | ixI == ixJ =
    (sigma' `isSubsetOf` sigma) && 
    isSubType vphi phi (ChST ixI ts sigma') (ChST ixJ ts' sigma')
  where
    vphi' = joinIndexVariables vphi $ Set.fromList ixI

isSubType _ _ _ _ = False


checkExp :: Set VarID -> Set NormalizedConstraint -> Map Var SType -> Exp -> Maybe SType
checkExp _ _ _ ZeroE = Just $ NatST zeroIndex zeroIndex
checkExp vphi phi gamma (SuccE e) =
  case checkExp vphi phi gamma e of
    Just (NatST ixI ixJ) -> Just $ NatST (ixI .+. oneIndex) (IxJ .+. oneIndex)
    _ -> Nothing
checkExp _ _ gamma (VarE v) = Map.lookup v gamma
checkExp _ _ _ _ = Nothing -- TODO: remember (S-sub) !!!

-- TODO: remember (S-subtype) !!!
checkProc :: Set VarID -> Set NormalizedConstraint -> Map Var SType -> Proc -> Maybe NormalizedIndex
checkProc _ _ _ NilP = Just zeroIndex
checkProc vphi phi gamma (TickP p) = checkProc vphi phi (Map.map (advance phi oneIndex) gamma) p >>= (\k -> Just $ k .+. oneIndex)
checkProc vphi phi gamma (ResP v t p) = checkProc vphi phi (Map.insert v t gamma) p
checkProc vphi phi gamma (InputP a vs p) | hasInputCapability a gamma = checkProc vphi phi (Map.map (advance phi ixI) gamma) p >>= (k -> Just $ k .+. ixI)
  where
    ixI = time a gamma