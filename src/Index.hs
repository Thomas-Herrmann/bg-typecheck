module Index
  ( Index (..),
    Term (..),
    Factor (..),
    subIndex,
  )
where

import GHC.Natural (Natural)

type VarID = Int

data Index = Term :+: Index | TerI Term deriving (Eq)

data Term = Factor :*: Term | FacI Factor deriving (Eq)

data Factor = NatI Natural | VarI VarID deriving (Eq)

instance Show Index where
  show (t :+: ixI) = show t ++ " + " ++ show ixI
  show (TerI t) = show t

instance Show Term where
  show (f :*: t) = show f ++ "*" ++ show t
  show (FacI f) = show f

instance Show Factor where
  show (NatI n) = show n
  show (VarI i) = "i" ++ show i

-- indices must be normalized prior
subIndex :: (Natural -> Natural -> Bool) -> Index -> Index -> Bool
subIndex comp (t :+: ixI) (t' :+: ixI') = subTerm comp t t' && subIndex comp ixI ixI'
subIndex comp ixI@(_ :+: _) t@(TerI _) = subIndex comp ixI $ FacI (NatI 0) :+: t
subIndex comp t@(TerI _) ixI@(_ :+: _) = subIndex comp (FacI (NatI 0) :+: t) ixI
subIndex comp (TerI t) (TerI t') = subTerm comp t t'

subTerm :: (Natural -> Natural -> Bool) -> Term -> Term -> Bool
subTerm comp (f :*: t) (f' :*: t') = subFactor comp f f' && subTerm comp t t'
subTerm _ _ _ = False

subFactor :: (Natural -> Natural -> Bool) -> Factor -> Factor -> Bool
subFactor comp (NatI n) (NatI m) = n `comp` m
subFactor comp (VarI i) (VarI j) = i == j
subFactor _ _ _ = False