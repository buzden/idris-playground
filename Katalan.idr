module Katalan

import Data.Nat

katalanTheorem : {x, y, z, t : Nat} -> x `GT` 1 -> y `GT` 1 -> z `GT` 1 -> t `GT` 1 ->
                 (x `power` y) = 1 + (z `power` t) -> (x=3, t=3, y=2, z=2)
