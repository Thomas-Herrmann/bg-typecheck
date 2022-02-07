module IndexNormalization
  ( normalize,
  )
where

import Constraint (Constraint)
import Index (Index (..))

normalize :: Index -> Index
normalize (FacI 0 _) = NatI 0
normalize (FacI 1 ixI) = normalize ixI
normalize (FacI n (AddI ixI ixJ)) = normalize $ AddI (FacI n ixI) (FacI n ixJ)
normalize (FacI n (FacI m ixI)) = normalize $ FacI (n * m) ixI
normalize (FacI n (NatI m)) = NatI $ n * m
normalize (AddI ixI ixJ) =
  case (normalize ixI, normalize ixJ) of
    (NatI n, NatI m) -> NatI $ n + m
    (NatI 0, ixJ) -> ixJ
    (ixI, NatI 0) -> ixI
    (ixI'@(NatI _), AddI ixJ' ixJ'') -> AddI ixJ' $ normalize (AddI ixI' ixJ'')
    (ixI'@(NatI _), ixJ') -> normalize $ AddI ixJ' ixI'
    (ixI', ixJ') -> AddI ixI' ixJ'
normalize ixI = ixI
