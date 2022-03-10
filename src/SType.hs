module SType
  ( SType (..),
    BType (..),
    IOCapability (..),
    SType.substituteVars,
  )
where

import Data.Set
import Index (NormalizedIndex (..), Subst, VarID, substituteVars)

data IOCapability = InputC | OutputC deriving (Eq, Ord)

data BType
  = NatBT NormalizedIndex NormalizedIndex
  | ListBT NormalizedIndex NormalizedIndex BType

data SType
  = BaseST BType
  | ChST NormalizedIndex [SType] (Set IOCapability)
  | ServST NormalizedIndex [VarID] NormalizedIndex [SType] (Set IOCapability)

substituteVars :: SType -> Subst -> SType
substituteVars (BaseST bType) subst = BaseST (substituteVarsB bType subst)
substituteVars (ChST ixI ts cap) subst = ChST (Index.substituteVars ixI subst) (Prelude.map (`SType.substituteVars` subst) ts) cap
substituteVars (ServST ixI is k ts cap) subst = ServST (Index.substituteVars ixI subst) is (Index.substituteVars k subst) (Prelude.map (`SType.substituteVars` subst) ts) cap

substituteVarsB :: BType -> Subst -> BType
substituteVarsB (NatBT ixI ixJ) subst = NatBT (Index.substituteVars ixI subst) (Index.substituteVars ixJ subst)
substituteVarsB (ListBT ixI ixJ bt) subst = ListBT (Index.substituteVars ixI subst) (Index.substituteVars ixJ subst) (substituteVarsB bt subst)