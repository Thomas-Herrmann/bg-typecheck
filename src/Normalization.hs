module Normalization
  ( normalize,
  )
where

import Constraint (Constraint (..))
import GHC.Natural (Natural)
import Index (Index (..))

normalizeIndex :: Index -> Index
normalizeIndex (FacI 0 _) = NatI 0
normalizeIndex (FacI 1 ixI) = normalizeIndex ixI
normalizeIndex (FacI n (AddI ixI ixJ)) = normalizeIndex $ AddI (FacI n ixI) (FacI n ixJ)
normalizeIndex (FacI n (FacI m ixI)) = normalizeIndex $ FacI (n * m) ixI
normalizeIndex (FacI n (NatI m)) = NatI $ n * m
normalizeIndex (AddI ixI ixJ) =
  case (normalizeIndex ixI, normalizeIndex ixJ) of
    (NatI n, NatI m) -> NatI $ n + m
    (NatI 0, ixJ) -> ixJ
    (ixI, NatI 0) -> ixI
    (ixI'@(NatI _), AddI ixJ' ixJ'') -> AddI ixJ' $ normalizeIndex (AddI ixI' ixJ'')
    (ixI'@(NatI _), ixJ') -> normalizeIndex $ AddI ixJ' ixI'
    (ixI', ixJ') -> AddI ixI' ixJ'
normalizeIndex ixI = ixI

normalize :: Constraint -> Constraint
normalize (Constraint (ixI, ixJ)) = Constraint (ixI', ixJ')
  where
    ixI' = normalizeIndex $ divideFactors divisor ixI
    ixJ' = normalizeIndex $ divideFactors divisor ixJ
    divisor = multiGCD $ factors ixI ++ factors ixJ

factors :: Index -> [Natural]
factors (FacI n _) = [n]
factors (AddI ixI ixJ) = factors ixI ++ factors ixJ
factors (NatI n) = [n]
factors _ = []

multiGCD :: [Natural] -> Natural
multiGCD [] = 1
multiGCD [n] = n
multiGCD (n : ns) = foldr gcd n ns

divideFactors :: Natural -> Index -> Index
divideFactors n (FacI m ixI) = FacI (m `div` n) ixI
divideFactors n (AddI ixI ixJ) = AddI (divideFactors n ixI) (divideFactors n ixJ)
divideFactors n (NatI m) = NatI $ m `div` n
divideFactors _ ixI = ixI