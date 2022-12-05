import Data.DPair

eexists : {f : a -> b -> Type} -> (Exists $ Exists . f) -> Nat

eeexists : {f : a -> b -> c -> Type} -> (Exists $ Exists . Exists .: f) -> Nat
