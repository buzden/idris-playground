module Proof

%default total
%access export

invert : (a : Nat) -> (b : Nat) -> (a + a = b + b) -> a = b
invert Z     Z     = const Refl
invert Z     (S k) = absurd . SIsNotZ . sym
invert (S k) Z     = absurd . SIsNotZ
invert (S k) (S j) = rewrite sym $ plusSuccRightSucc k k in rewrite sym $ plusSuccRightSucc j j in
                     eqSucc k j . invert k j . succInjective (k+k) (j+j) . succInjective (S $ k+k) (S $ j+j)
