module Normalization
  ( normalize,
  )
where

import Constraint (Constraint (..))
import GHC.Natural (Natural)
import Index (Factor (..), Index (..), Term (..))

reduceStepAll :: Index -> Index
reduceStepAll ixI
  | ixI' == ixI = ixI
  | otherwise = reduceStepAll ixI'
  where
    ixI' = reduceIndex ixI

reduceIndex :: Index -> Index
reduceIndex (FacI (NatI 0) :+: ixI) = ixI
reduceIndex (FacI (NatI n) :+: TerI (FacI (NatI m))) = TerI $ FacI (NatI (n + m))
reduceIndex (FacI (NatI n) :+: (FacI (NatI m) :+: ixI)) = FacI (NatI (n + m)) :+: ixI
reduceIndex (t :+: ixI) = reduceTerm t :+: reduceIndex ixI
reduceIndex (TerI t) = TerI $ reduceTerm t

reduceTerm :: Term -> Term
reduceTerm (NatI 0 :*: _) = FacI $ NatI 0
reduceTerm (NatI 1 :*: t) = t
reduceTerm (NatI n :*: FacI (NatI m)) = FacI $ NatI (n * m)
reduceTerm (NatI n :*: (NatI m :*: FacI f)) = NatI (n * m) :*: FacI f
reduceTerm t = t

-- TODO: sort

normalize :: Constraint -> Constraint
normalize (Constraint (ixI, ixJ)) = Constraint (ixI', ixJ')
  where
    ixI' = reduceStepAll $ divideFactors divisor ixI
    ixJ' = reduceStepAll $ divideFactors divisor ixJ
    divisor = multiGCD $ factors ixI ++ factors ixJ

factors :: Index -> [Natural]
factors (t :+: ixI) = factor t : factors ixI
factors (TerI t) = [factor t]

factor :: Term -> Natural
factor (NatI n :*: _) = n
factor (FacI (NatI n)) = n
factor _ = 1

multiGCD :: [Natural] -> Natural
multiGCD [] = 1
multiGCD [n] = n
multiGCD (n : ns) = foldr gcd n ns

divideFactors :: Natural -> Index -> Index
divideFactors n (t :+: ixI) = divideFactor n t :+: divideFactors n ixI
divideFactors n (TerI t) = TerI $ divideFactor n t

divideFactor :: Natural -> Term -> Term
divideFactor n (NatI m :*: t) = NatI (m `div` n) :*: t
divideFactor n (FacI (NatI m)) = FacI $ NatI (m `div` n)
divideFactor _ t = t