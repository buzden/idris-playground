f : Nat
f = X.z where
  namespace X
    public export
    z : Nat
    z = 10

f' : Nat
f' = X.z where
  namespace X
    public export
    z : Nat
    z = 10

g : Nat
g = let namespace X
          public export
          w : Nat
          w = 10
    in X.w
