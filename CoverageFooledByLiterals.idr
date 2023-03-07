failing
  f : (n : Nat) -> (Void, Void) -> Nat
  f 0 (_, _) impossible
  f 1 (_, _) impossible
  f (S k) x = 5

f : (n : Nat) -> (Void, Void) -> Nat
f Z     (_, _) impossible
f (S Z) (_, _) impossible
f (S k) x = 5
