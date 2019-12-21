module Preloaded

%access public export
%default total

fibAux : Nat -> Nat -> Nat -> Nat
fibAux a b Z = a
fibAux a b (S n) = fibAux b (a + b) n

fib2 : Nat -> Nat
fib2 = fibAux 0 1
