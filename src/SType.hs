module SType
  ( SType (..),
    IOCapability (..),
    SType.substituteVars,
  )
where

import Data.Set
import Index (NormalizedIndex (..), Subst, VarID, substituteVars)

data IOCapability = InputC | OutputC deriving (Eq, Ord, Show)

data SType
  = NatST NormalizedIndex NormalizedIndex
  | ChST NormalizedIndex [SType] (Set IOCapability)
  | ServST NormalizedIndex [VarID] NormalizedIndex [SType] (Set IOCapability)
  | LockedServST NormalizedIndex [VarID] NormalizedIndex [SType] (Set IOCapability) NormalizedIndex
  deriving (Show)

substituteVars :: SType -> Subst -> SType
substituteVars (NatST ixI ixJ) subst = NatST (Index.substituteVars ixI subst) (Index.substituteVars ixJ subst)
substituteVars (ChST ixI ts cap) subst = ChST (Index.substituteVars ixI subst) (Prelude.map (`SType.substituteVars` subst) ts) cap
substituteVars (ServST ixI is ixK ts cap) subst = ServST (Index.substituteVars ixI subst) is (Index.substituteVars ixK subst) (Prelude.map (`SType.substituteVars` subst) ts) cap
substituteVars (LockedServST ixI is ixK ts cap ixJ) subst = LockedServST (Index.substituteVars ixI subst) is (Index.substituteVars ixK subst) (Prelude.map (`SType.substituteVars` subst) ts) cap (Index.substituteVars ixJ subst)
