f : (Nat, Nat) -> Nat
f pair = let 0 (x, y) = pair
         in x

record R where
  constructor MkR
  0 erased : Nat
  1 linear : Nat
  omega : Nat

r0 : R -> Nat
r0 r = let 0 MkR e l o = r in ?foo_0
       -- I'd expect all `e`, `l` and `o` be 0

r1 : R -> Nat
r1 r = let 1 MkR e l o = r in ?foo_1
       -- I'd expect `e` be `0` and `l` and `o` be `1`

rO : R -> Nat
rO r = let MkR e l o = r in ?foo_O
       -- I'd expext `e` be `0`, `l` be `1` and `o` be omega
