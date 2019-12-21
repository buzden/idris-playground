module Fib

import FibPreloaded

{-
Preloaded:

module Preloaded

%access public export
%default total

fibAux : Nat -> Nat -> Nat -> Nat
fibAux a b Z = a
fibAux a b (S n) = fibAux b (a + b) n

fib2 : Nat -> Nat
fib2 = fibAux 0 1
-}

%access export
%default total

fibEq : (n : Nat) -> fib2 n = fib n
fibEq n = ?write_a_proof
