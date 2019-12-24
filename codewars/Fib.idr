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
fibEq = auxInter Z where
  auxInter : (l, k : Nat) -> fibAux 0 1 (l + k) = fibAux (fib k) (fib (S k)) l
  auxInter l Z     = rewrite plusZeroRightNeutral l in Refl
  auxInter l (S k) = rewrite sym $ plusSuccRightSucc l k in
                     rewrite plusCommutative (fib (S k)) (fib k) in
                     auxInter (S l) k
