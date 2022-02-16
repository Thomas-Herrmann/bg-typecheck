module PiCalculus 
( Var,
  Exp (..),
  Proc (..),
) where

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
    | OutputP Var [Exp] Proc
    | RInputP Var [Var] Proc
    | ResP Var SType Proc
    | MatchP Exp Proc Var Proc
