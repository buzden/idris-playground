f1 : Nat
f1 = g1 where
  g1 : Nat
  g1 = 5

f2 : Nat
f2 = g2 where
  namespace X
    export
    g2 : Nat
    g2 = 5

--f3 : Integer -> Nat
--f3 x = g3 where
--  namespace Y
--    export
--    g3 : Nat
--    g3 = 4

f4 : Integer -> Nat
f4 x = g4 x where
  namespace Z
    export
    g4 : Nat
    g4 _ = 4
