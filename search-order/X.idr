module X

public export
data Ty : Type where
  A : Ty
  B : Ty

public export
f : (d : Ty) => Nat -> Ty
f _ = d

g : f 0 = B
g = Refl
