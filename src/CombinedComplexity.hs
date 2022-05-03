module CombinedComplexity
  ( CombinedComplexity,
    emptyComplexity,
    singleComplexity,
    (.+.),
    basis,
  )
where

import Constraint
import Data.Set as Set
import qualified Index

type CombinedComplexity = Set Index.NormalizedIndex

emptyComplexity = Set.empty

singleComplexity = Set.singleton

(.+.) :: CombinedComplexity -> Index.NormalizedIndex -> CombinedComplexity
(.+.) cc ix = Set.map (Index..+. ix) cc

basis :: Set Index.VarID -> Set NormalizedConstraint -> CombinedComplexity -> CombinedComplexity
basis vphi phi cc = _
