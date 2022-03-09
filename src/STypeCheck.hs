module STypeCheck
  (
  )
where

import Constraint (Constraint (..), NormalizedConstraint (..))
import ConstraintInclusion (constraintsContained)
import Data.Map as Map
import Data.Set as Set
import Index (NormalizedIndex, VarID, equalsConstant, evaluate, oneIndex, zeroIndex, (.*.), (.+.), (.-.), (./.))
import Normalization (normalize, normalizeIndex)
import PiCalculus (Exp (..), Proc (..), Var)
import SType (BType (..), SType (..))

-- note that we use meta-variables I,J,K,L for normalized indices in this file

advance :: Set NormalizedConstraint -> NormalizedIndex -> SType -> Maybe SType
advance _ _ nat@(NatST _ _) = Just nat
advance phi ixI (ChST ixJ ts) | constraintsContained phi (normalize $ ixJ :>=: ixI) = Just $ ChST (ixJ .-. ixI) ts
advance phi ixI (IChST ixJ ts) | constraintsContained phi (normalize $ ixJ :>=: ixI) = Just $ IChST (ixJ .-. ixI) ts
advance phi ixI (OChST ixJ ts) | constraintsContained phi (normalize $ ixJ :>=: ixI) = Just $ OChST (ixJ .-. ixI) ts
advance phi ixI ServST ixJ is ixK ts
  | constraintsContained phi (normalize $ ixJ :>=: ixI) = Just $ ServST (ixJ .-. ixI) is ixK ts
  | otherwise = Just $ OServST (ixJ .-. ixI) is ixK ts
advance phi ixI IServST ixJ is ixK ts | constraintsContained phi (normalize $ ixJ :>=: ixI) = Just $ IServST (ixJ .-. ixI) is ixK ts
advance phi ixI OServST ixJ is ixK ts = Just $ OServST (ixJ .-. ixI) is ixK ts
advance _ _ _ = Nothing

defaultBaseType = NatBT zeroIndex zeroIndex

isSubType :: Set VarID -> Set NormalizedConstraint -> SType -> SType -> Bool
isSubType _ _ _ _ = False

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
-- (S-CONS-1) + (S-CONS-2)
checkExp vphi phi gamma (ListE (e : e')) = do
  (BaseST b) <- checkExp vphi phi gamma e
  (BaseST (ListBT ixI ixJ b')) <- checkExp vphi phi gamma (ListE e')
  if equalsConstant ixI 1 && equalsConstant ixJ 1
    then -- (S-CONS-2)
      return $ BaseST (ListBT oneIndex oneIndex b)
    else -- (S-CONS-1)

      if isSubType vphi phi (BaseST b') (BaseST b)
        then return $ BaseST (ListBT (ixI .+. oneIndex) (ixJ .+. oneIndex) b)
        else Nothing

-- TODO: remember (S-subtype) !!!
checkProc :: Set VarID -> Set NormalizedConstraint -> Map Var SType -> Proc -> Maybe NormalizedIndex
checkProc _ _ _ NilP = Just zeroIndex
checkProc vphi phi gamma (TickP p) = checkProc vphi phi (Map.map (advance phi oneIndex) gamma) p >>= (\k -> Just $ k .+. oneIndex)
checkProc vphi phi gamma (ResP v t p) = checkProc vphi phi (Map.insert v t gamma) p
checkProc vphi phi gamma (InputP a vs p) | hasInputCapability a gamma = checkProc vphi phi (Map.map (advance phi ixI) gamma) p >>= (k -> Just $ k .+. ixI)
  where
    ixI = time a gamma