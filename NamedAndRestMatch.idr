%default total

data X : Type where
  MkX : (a : Nat) -> (b : Nat) -> X

f : X -> Nat
f $ MkX {a} {} = ?foo
