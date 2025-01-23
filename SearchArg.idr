data X : Type where
  [noHints]
  MkX : X

f : (x : X) -> Nat
f _ = let y : X = %search
      in ?foo

g : (x : X) -> let y : X = %search in Nat
g _ = 5
