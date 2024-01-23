%default total

f : (x : Nat) -> {default x y : Nat} -> Nat
f x = y

g : Nat
g = f 5 {y=6}

h : Nat
h = f 5
