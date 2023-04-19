g : Nat -> Nat -> Nat
g (x + 1) 2 = 3
g _ _ = 4

f : Nat -> Nat -> Nat
f (f x 1) 2 = 3
f _ _ = 4

h : Nat -> Nat -> Nat
h (f x 1) 2 = 3
h _ _ = 4
