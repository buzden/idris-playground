module RecordInWhere

import Data.Vect

f1 : Int
f1 = 5 where
  data X : Type where
    MkX : (a : Int) -> X

f2 : Int
f2 = 5 where
  record X where
    constructor MkX
    a : Int

f3 : Nat -> Int
f3 x = 5 where
  data X : Type where
    MkX : (a : Int) -> X

f4 : Nat -> Int
f4 x = 5 where
  data X : Type where
    MkX : (a : Vect x Int) -> X

f5 : Nat -> Int
f5 x = 5 where
  record X5 where
    constructor MkX5
    a : Int

f6 : Nat -> Int
f6 x = 5 where
  record X6 where
    constructor MkX6
    a : Vect x Int
