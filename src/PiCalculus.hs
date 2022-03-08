module PiCalculus
  ( Var,
    Exp (..),
    Proc (..),
  )
where

import Index (Subst)
import SType (SType)

type Var = String

data Exp
  = ZeroE
  | SuccE Exp
  | VarE Var

data Proc
  = NilP
  | TickP Proc
  | Proc :|: Proc
  | InputP Var [Var] Proc
  | OutputP Var [Exp] Subst
  | RepInputP Var [Var] Proc
  | RestrictP Var SType Proc
  | MatchNatP Exp Proc Var Proc
  | MatchListP Exp Proc Var Var Proc
