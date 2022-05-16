module Proof

import Data.Nat

%default total

export
invert : (a : Nat) -> (b : Nat) -> (a + a = b + b) -> a = b
invert Z     Z     = const Refl
invert Z     (S k) = absurd . SIsNotZ . (\x => sym x)
invert (S k) Z     = absurd . SIsNotZ
invert (S k) (S j) = rewrite sym $ plusSuccRightSucc k k in rewrite sym $ plusSuccRightSucc j j in
                     eqSucc k j . invert k j . injective . injective
