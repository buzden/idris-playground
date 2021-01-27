module Blackbird

import Data.Nat

f : Nat -> Nat -> Nat
f = (+1) .: (+) . (+1)

g : Nat -> Nat -> Nat
-- instead of `g = (+1) . (+1) .: (+)` write, since double `.:` works for any priority and "`.` then `.:`" works only when `.:` has smaller priority.
g = (+1) .: (+1) .: (+)

-- Assumes that `.:` has the same priority as `.`
x : String -> List String -> String
x = concatMap . (++ "e") .: (++) . (++ "x")
