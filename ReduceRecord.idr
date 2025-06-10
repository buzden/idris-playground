%default total

record X where
  constructor MkX
  a : Nat
  b : List Nat

f : List Nat -> X -> X
f xs = {a $= S, b := xs}

g : List Nat -> X -> X
g xx z = do
  let x : X
      x = f xx z
  --let MkX {} = z
  let u : (x.b = xx) := Refl
  ?foo
