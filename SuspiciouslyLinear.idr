import Data.Vect

f1 : (n : Nat) -> Vect n Nat -> Vect (S n) Nat
f1 a b = a :: b

f2 : (n : Nat) -> case n of
  k => Vect k Nat -> Vect (S k) Nat
f2 a b = a :: b

f3 : (n : Nat) -> case n of
  Z => Vect Z Nat -> Vect (S Z) Nat
  (S k) => Vect (S k) Nat -> Vect (S (S k)) Nat
f3 Z b = a :: b
f3 (S a) b = a :: b

f4 : (n : (Nat, Nat)) -> case n of
  (x, y) => Vect x Nat -> Vect (S x) Nat
f4 (_, a) b = a :: b
