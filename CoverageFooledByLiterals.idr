data X : Nat -> Type where
  X3 : X 3
  X4 : X 4

failing
  f : (n : Nat) -> (X n, X n) -> Nat
  f 0 (_, _) impossible
  f 1 (_, _) impossible
  f (S k) x = 5

f : (n : Nat) -> (X n, X n) -> Nat
f Z     (_, _) impossible
f (S Z) (_, _) impossible
f (S k) x = 5

