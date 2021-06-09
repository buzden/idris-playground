import Data.Nat

p1_equals_s : (1+) = S
p1_equals_s = Refl

funext : {p, q : a -> b} -> ((x : a) -> p x = q x) -> p = q
funext _ = believe_me (Z = Z)

onep_equals_s : (+1) = S
onep_equals_s = funext \x => plusCommutative x 1
