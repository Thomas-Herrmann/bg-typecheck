module STypeCheck
  (
  )
where

import Constraint (NormalizedConstraint (..), Constraint (..))
import Normalization (normalize, normalizeIndex)
import Index (NormalizedIndex, VarID, zeroIndex, oneIndex, (.+.), (.-.), (.*.), (./.))
import ConstraintInclusion (constraintsContained)
import PiCalculus (Var, Exp(..), Proc(..))
import SType (SType (..))
import Data.Set as Set
import Data.Map as Map


-- note that we use meta-variables I,J,K,L for normalized indices in this file


advance :: Set NormalizedConstraint -> NormalizedIndex -> SType -> Maybe SType
advance _ _ nat@(NatST _ _) = Just nat
advance phi ixI (ChST ixJ ts) | constraintsContained phi (normalize $ ixJ :>=: ixI) = Just $ ChST (ixJ .-. ixI) ts
advance phi ixI (IChST ixJ ts) | constraintsContained phi (normalize $ ixJ :>=: ixI) = Just $ IChST (ixJ .-. ixI) ts
advance phi ixI (OChST ixJ ts) | constraintsContained phi (normalize $ ixJ :>=: ixI) = Just $ OChST (ixJ .-. ixI) ts
advance phi ixI ServST ixJ is ixK ts | constraintsContained phi (normalize $ ixJ :>=: ixI) = Just $ ServST (ixJ .-. ixI) is ixK ts
                                     | otherwise = Just $ OServST (ixJ .-. ixI) is ixK ts
advance phi ixI IServST ixJ is ixK ts | constraintsContained phi (normalize $ ixJ :>=: ixI) = Just $ IServST (ixJ .-. ixI) is ixK ts
advance phi ixI OServST ixJ is ixK ts = Just $ OServST (ixJ .-. ixI) is ixK ts                                     
advance _ _ _ = Nothing


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