module Normalization
  ( normalize,
  )
where

import Constraint (Constraint (..))
import Data.List (sort)
import GHC.Natural (Natural)
import Index (Index (..), Term (..))


-- index must be sorted prior
reduceIndex :: Index -> Index
reduceIndex (n :+: ((0 :*: _) : ts)) = reduceIndex $ n :+: ts
reduceIndex (n :+: ((m :*: is) : (m' :*: js) : ts)) | is == js = reduceIndex $ n :+: (((m + m') :*: is) : ts)
reduceIndex ixI = ixI


sortIndex :: Index -> Index
sortIndex (n :+: ts) = n :+: sort (Prelude.map sortCoefficients ts)
  where
    sortCoefficients (m :*: (i, is)) =
      let
        i' : is' = sort $ i : is
      in
        m :*: (i', is')


normalize :: Constraint -> Constraint
normalize (ixI :<=: ixJ) = ixI'' :<=: ixJ''
  where
    ixI' = (reduceIndex . sortIndex) ixI
    ixJ' = (reduceIndex . sortIndex) ixJ
    divisor = multiGCD $ factors ixI' ++ factors ixJ'
    ixI'' = divideFactors divisor ixI'
    ixJ'' = divideFactors divisor ixJ'

factors :: Index -> [Natural]
factors (n :+: ts) = n : Prelude.map (\(m :*: _) -> m) ts

multiGCD :: [Natural] -> Natural
multiGCD [] = 1
multiGCD [n] = n
multiGCD (n : ns) = foldr gcd n ns

divideFactors :: Natural -> Index -> Index
divideFactors n (m :+: ts) = (m `div` n) :+: Prelude.map (\(m' :*: is) -> (m' `div` n) :*: is) ts