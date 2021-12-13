f1 : Nat
f1 = g where
  namespace X
    export
    g : Nat
    g = 5

f3 : Nat
f3 = Main.X.g

f2 : Nat
f2 = g where
  namespace X
    export
    g : Nat
    g = 5
