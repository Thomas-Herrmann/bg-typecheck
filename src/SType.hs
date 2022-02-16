module SType
( SType (..),

) where


data SType 
  = NatST NormalizedIndex NormalizedIndex
  | ChST NormalizedIndex [SType]
  | IChST NormalizedIndex [SType]
  | OChST NormalizedIndex [SType]
  | ServST NormalizedIndex [VarID] NormalizedIndex [SType]
  | IServST NormalizedIndex [VarID] NormalizedIndex [SType]
  | OServST NormalizedIndex [VarID] NormalizedIndex [SType]