module Intervals
  (
  )
where

import Constraint (Constraint, NormalizedConstraint (..))
import Data.Set as Set
import GHC.Natural (Natural)
import Index (NormalizedIndex (..), VarID, substitute)

data Interval
  = EmptyI
  | PairI Natural Natural
  | InfI Natural
  deriving (Eq)

intersect :: Interval -> Interval -> Interval
intersect EmptyI _ = EmptyI
intersect _ EmptyI = EmptyI
intersect (InfI n) (PairI n' m)
  | m < low = EmptyI -- disjoint
  | otherwise = PairI low m
  where
    low = max n n'
intersect (PairI n m) (InfI n')
  | m < low = EmptyI -- disjoint
  | otherwise = PairI low m
  where
    low = max n n'
intersect (InfI n) (InfI n') = InfI $ max n n'
intersect (PairI n m) (PairI n' m')
  | high < low = EmptyI -- disjoint
  | otherwise = PairI low high
  where
    low = max n n'
    high = min m m'

-- intervals within one list must be disjoint;
-- lists of intervals must be sorted in ascending fashion (trivial as intervals are disjoint)
intersectIntervals :: [Interval] -> [Interval] -> [Interval]
intersectIntervals [] _ = []
intersectIntervals _ [] = []
intersectIntervals (EmptyI : is1') is2 = intersectIntervals is1' is2
intersectIntervals is1 (EmptyI : is2') = intersectIntervals is1 is2'
intersectIntervals is1@(InfI n : _) (PairI n' m : is2') = PairI (max n n') m : intersectIntervals is1 is2'
intersectIntervals (PairI n m : is1') is2@(InfI n' : _) = PairI (max n n') m : intersectIntervals is1' is2
intersectIntervals (InfI n : _) (InfI n' : _) = [InfI $ max n n']
intersectIntervals (i1@(PairI n m) : is1') (i2@(PairI n' m') : is2') =
  case i1 `intersect` i2 of
    EmptyI ->
      if m > m'
        then intersectIntervals (i1 : is1') is2'
        else intersectIntervals is1' (i2 : is2')
    ires ->
      if m > m'
        then ires : intersectIntervals (i1 : is1') is2'
        else ires : intersectIntervals is1' (i2 : is2')

containsIntervals :: [Interval] -> [Interval] -> Bool
containsIntervals _ [] = True
containsIntervals (EmptyI : is1') is2 = containsIntervals is1' is2
containsIntervals is1 (EmptyI : is2') = containsIntervals is1 is2'
containsIntervals [] _ = False -- the ordering is important, as is1 = [] and is2 = [EmptyI,..,EmptyI] should be true
containsIntervals (i1 : is1') (i2 : is2') =
  if (i1 `intersect` i2) == i2
    then containsIntervals (i1 : is1') is2'
    else containsIntervals is1' (i2 : is2')

findIntervals :: VarID -> NormalizedConstraint -> [Interval]
findIntervals i c = 

checkJudgement :: VarID -> Set NormalizedConstraint -> NormalizedConstraint -> Bool
checkJudgement i phi c = containsIntervals (findIntervals i c) satisfiedIntervals
  where
    satisfiedIntervals = Set.foldr (\c' isRes -> intersectIntervals isRes $ findIntervals i c') [InfI 0] phi