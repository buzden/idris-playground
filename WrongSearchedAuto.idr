data X : Type

someX : X

data Y : Type

fun : X -> (X -> Y) => Nat

f1 : (X -> Y) => Nat
f1 = fun someX + 5

f1' : Integer -> (X -> Y) => Nat
f1' _ = fun someX + 5

failing "Can't find an implementation for Y"
  f2 : X -> (X -> Y) => Nat
  f2 _ = fun someX + 5

failing "Can't find an implementation for Y"
  f2' : (X -> Y) => X -> Nat
  f2' _ = fun someX + 5

f3 : X -> Y => Nat
f3 _ = fun someX + 5
