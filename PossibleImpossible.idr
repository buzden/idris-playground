%default total

data Even : Nat -> Type where
  EZ  : Even Z
  ESS : Even n -> Even (2 + n)

data Odd : Nat -> Type where
  OSZ : Odd 1
  OSS : Odd n -> Odd (2 + n)

notE : (n : Nat) -> Not (Even n, Odd n)
notE Z         (_, _) impossible
notE (S Z)     (_, _) impossible
notE (S $ S n) (ESS n, OSS n) impossible
