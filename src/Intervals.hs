module Intervals
  ( checkJudgement,
  )
where

import Constraint (Constraint, NormalizedConstraint (..))
import Data.Functor ((<&>))
import Data.Map as Map
import Data.MultiSet as MultiSet
import Data.Set as Set
import Diagrams.Solve.Polynomial (quartForm)
import Index (NormalizedIndex (..), VarID, substitute)

data Interval
  = EmptyI
  | PairI Float Float
  | InfI Float
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

findIntervals :: VarID -> NormalizedConstraint -> Maybe [Interval]
findIntervals i (NormalizedConstraint f)
  | invalidPolynomial = Nothing
  | otherwise = do
    roots <- nonnegativeRoots i f
    case roots of
      [] -> substitute f (Map.singleton i 0) >>= (\n -> return [InfI 0 | n < 0])
      _ ->
        let (lastRoot, intervals) = Prelude.foldr foldRoot (0, []) roots
         in substitute f (Map.singleton i (lastRoot + 1)) >>= (\n -> return $ intervals ++ [InfI lastRoot | n < 0])
  where
    foldRoot high (low, intervals)
      | ((low + high) / 2) <= 0 = (high, PairI low high : intervals)
      | otherwise = (high, intervals)

    joinIntervals [] = []
    joinIntervals (EmptyI : intervals') = joinIntervals intervals'
    joinIntervals (PairI low high : PairI low' high' : intervals') | high >= low' = joinIntervals $ PairI low high' : intervals'
    joinIntervals (PairI low high : InfI low' : intervals') | high >= low' = [InfI low]
    joinIntervals (InfI low : intervals') = [InfI low]
    joinIntervals (interval : intervals') = interval : joinIntervals intervals'

    invalidPolynomial =
      Prelude.foldr (\ms b -> not b || (not (MultiSet.null ms) && MultiSet.distinctElems ms /= [i])) True $ Map.keys f

nonnegativeRoots :: VarID -> NormalizedIndex -> Maybe [Float]
nonnegativeRoots i f
  | isConstant = Just []
  | invalidPolynomial || tooHighDegree = Nothing
  | otherwise = Just $ Prelude.filter (0 <=) roots
  where
    isConstant =
      case Map.keys f of
        [] -> True
        [ms] -> Prelude.null $ MultiSet.elems ms
        _ -> False

    tooHighDegree =
      Prelude.foldr ((||) . ((4 <) . MultiSet.size)) False (Map.keys f)

    invalidPolynomial =
      Prelude.foldr (\ms b -> not b || (not (MultiSet.null ms) && MultiSet.distinctElems ms /= [i])) True $ Map.keys f

    coeff n =
      case Map.lookup (MultiSet.fromList $ Prelude.take n [i, i ..]) f of
        Just m -> fromIntegral m
        _ -> 0

    roots = quartForm (coeff 0) (coeff 1) (coeff 2) (coeff 3) (coeff 4)

checkJudgement :: VarID -> Set NormalizedConstraint -> NormalizedConstraint -> Bool
checkJudgement i phi c =
  case (satisfiedIntervals, findIntervals i c) of
    (Just isGiven, Just isNew) -> containsIntervals isNew isGiven
    _ -> False
  where
    satisfiedIntervals = Set.foldr (\c' misRes -> misRes >>= (\isRes -> findIntervals i c' <&> intersectIntervals isRes)) (Just [InfI 0]) phi