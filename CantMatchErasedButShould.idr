%default total

data Y : Bool -> Type where
  T : Y True
  F : Y True -> Y False

a : (0 _ : Y True) -> Unit
a T = ()

b : (0 _ : Y False) -> Unit
b (F T) = ()

data X : Nat -> Type where
  N : X Z
  C : X n -> X (S n)
  --C : {n : _} -> X n -> X (S n)

g : (0 _ : X 0) -> Unit
g N = ()

f : (0 _ : X 1) -> Unit
f (C x) = ()

total
h' : (_ : X 1) -> Unit
h' (C N) = ()

h : (0 _ : X 1) -> Unit
h (C N) = ?foo
