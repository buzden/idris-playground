-- To be type-checked by Idris 2 --
-- Idea origin: @greenest_pig

module MonoidRegardingToFunction

import Data.Nat

--- Interfaces for lawful semigroup and monoid ---

interface S (a : Type) (op : a -> a -> a) where
  opAssoc : (x, y, z : a) -> x `op` (y `op` z) = (x `op` y) `op` z

interface S a op => M (a : Type) (op : a -> a -> a) where
  neu  : a
  neuL : (x : a) -> neu `op` x = x
  neuR : (x : a) -> x `op` neu = x

--- Additive monoid for naturals ---

S Nat (+) where
  opAssoc = plusAssociative

M Nat (+) where
  neu = 0
  neuL _ = Refl
  neuR n = rewrite plusZeroRightNeutral n in Refl

--- Multiplicative monoid for naturals ---

S Nat (*) where
  opAssoc = multAssociative

M Nat (*) where
  neu = 1
  neuL n = rewrite plusZeroRightNeutral n in Refl
  neuR n = rewrite multOneRightNeutral n in Refl

--- Usage example ---

fold : {op : a -> a -> a} -> M a op => List a -> a
fold [] = neu {a} {op}
fold (x::xs) = x `op` fold {op} xs

--- Running example ---

testList : List Nat
testList = [1, 2, 3, 4]

testSum : Nat
testSum = fold {op=(+)} testList
-- it is 10!

testMul : Nat
testMul = fold {op=(*)} testList
-- it is 24!
