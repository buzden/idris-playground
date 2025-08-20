%default total

T : Bool -> Type
T True  = (a : Nat) -> {b : Nat} -> Nat
T False = (c : Nat) -> Nat

f : (b : Bool) -> T b

g : Nat
g = f True {b = 5} {a = 4}
g = f False 4
