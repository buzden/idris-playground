public export
data X : Type where
  [noHints]
  U : X
  W : X

public export %hint
xHint : X
-- Intentionally unimplemented

f : Int -> X => Int
f a = a + 1

g : Int
g = f 4
-- Typechecks even when `xHint` is unimplemented.
