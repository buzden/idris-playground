%default total

Y : {n : Unit} -> Type
record X where
  constructor MkX
  r : Y {n=u} -> Nat
Y {n=MkUnit} = X

toY : X -> Y {n}
toY {n=()} = id

f : X -> Nat
f c = r c $ toY c

loop : Nat
loop = f $ MkX {u=()} f
