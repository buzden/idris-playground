import Data.Vect

f : {n : Nat} -> Vect n Nat
f = replicate _ 0

d : Vect n Nat -> Nat
d = foldl (+) 0

failing
  z : Nat
  z = d f
