module Minus

import Data.Nat

plus_mult : (n, m, k : Nat) -> {auto km : k `LTE` m} -> n + (m `minus` k) = (m + n) `minus` k
plus_mult n m Z = rewrite minusZeroRight m in
                  rewrite minusZeroRight $ m + n in
                  rewrite plusCommutative m n in
                  Refl
plus_mult n (S m) (S k) {km=LTESucc _} = plus_mult n m k

%hint
power2_ge_1 : (n : Nat) -> 1 `LTE` (2 `power` n)
power2_ge_1 Z     = LTESucc LTEZero
power2_ge_1 (S n) = lteTransitive (power2_ge_1 n) $ lteAddRight (2 `power` n)
