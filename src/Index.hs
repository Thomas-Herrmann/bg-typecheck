module Index
  ( Index (..),
    subIndex,
  )
where

import GHC.Natural (Natural)

type VarID = Int

data Index
  = VarI VarID
  | NatI Natural
  | AddI Index Index
  | FacI Natural Index
  deriving (Eq)

instance Show Index where
  show (VarI id) = "i" ++ show id
  show (NatI n) = show n
  show (AddI ixI ixJ) = show ixI ++ " + " ++ show ixJ
  show (FacI n (AddI ixI ixJ)) = show n ++ "*(" ++ show ixI ++ " + " ++ show ixJ ++ ")"
  show (FacI n ixI) = show n ++ "*" ++ show ixI

subIndex :: (Natural -> Natural -> Bool) -> Index -> Index -> Bool
subIndex comp (NatI n) (NatI m) = n `comp` m
subIndex _ (VarI id) (VarI id') = id == id'
subIndex comp (AddI ixI ixJ) (AddI ixI' ixJ') = subIndex comp ixI ixI' && subIndex comp ixJ ixJ'
subIndex comp (FacI n ixI) (FacI m ixI') = n `comp` m && subIndex comp ixI ixI'
subIndex _ _ _ = False