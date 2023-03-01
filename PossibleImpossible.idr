data Even : Nat -> Type where
  EZ  : Even Z
  ESS : Even n -> Even (2 + n)

notE : (n : Nat) -> Not (Even n)
notE (S $ S n) (ESS n) impossible
notE 0 EZ = notE 2 (ESS EZ)
