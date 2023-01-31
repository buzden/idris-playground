f : Nat -> Nat -> Nat
f _ 0 = 1
f 0 _ = 2
f _ 1 = 3
f 1 _ = 4
f (S $ S n) (S $ S m) = 5
