module FibGCD

import Data.Nat

import Decidable.Equality

fib : Nat -> Nat
fib 0 = 0
fib 1 = 1
fib (S $ S n) = fib (S n) + fib n

%hint
fib_isSucc : (n : Nat) -> IsSucc n => IsSucc (fib n)

fib_gcd : {n, m : Nat} -> case fib_isSucc (S n) of ItIsSucc => gcd {ok=LeftIsNotZero} (fib $ S n) (fib $ S m) = fib (gcd (S n) (S m))
