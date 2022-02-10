module Index
  ( Index (..),
    Term (..),
    subIndex,
    VarID,
  )
where

import Data.List (intercalate)
import GHC.Natural (Natural)

type VarID = Int

data Index = Natural :+: [Term] deriving (Eq, Ord)

data Term = Natural :*: (VarID, [VarID]) deriving (Eq)

instance Show Index where
  show (n :+: ts) = show n ++ " + " ++ intercalate " + " (Prelude.map show ts)

instance Show Term where
  show (n :*: (i, is)) = show n ++ "*i" ++ intercalate "*i" (Prelude.map show (i : is))

instance Ord Term where
  (n :*: (i, is)) `compare` (m :*: (j, js)) =
    case (i : is) `compare` (j : js) of
      LT -> LT
      GT -> GT
      EQ -> n `compare` m

-- indices must be normalized prior
subIndex :: Index -> Index -> Bool
subIndex (n :+: ts) (m :+: ts') = n <= m && Prelude.foldr pairwiseSubTerm True (Prelude.zip ts ts')
  where
    pairwiseSubTerm (t, t') b = b && subTerm t t'

subTerm :: Term -> Term -> Bool
subTerm (n :*: (i, is)) (m :*: (j, js)) = n <= m && Prelude.foldr (\(k, l) b -> b && k == l) True (Prelude.zip (i : is) (j : js))
