module Index
  ( Index (..),
  )
where

import GHC.Natural (Natural, naturalFromInteger)

type VarID = Int

data Index
  = VarI VarID
  | NatI Natural
  | AddI Index Index
  | FacI Natural Index

instance Show Index where
  show (VarI id) = "i" ++ show id
  show (NatI n) = show n
  show (AddI ixI ixJ) = show ixI ++ " + " ++ show ixJ
  show (FacI n (AddI ixI ixJ)) = show n ++ "*(" ++ show ixI ++ " + " ++ show ixJ ++ ")"
  show (FacI n ixI) = show n ++ "*" ++ show ixI