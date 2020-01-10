module Proof

%default total
%access export

lemma : (a : Nat) -> (b : Nat) -> S a + S a = S b + S b -> a + a = b + b
lemma a b = rewrite sym $ plusSuccRightSucc a a in
            rewrite sym $ plusSuccRightSucc b b in
            succInjective (a + a) (b + b) . succInjective (S (a + a)) (S (b + b))

invert : (a : Nat) -> (b : Nat) -> (a + a = b + b) -> a = b
invert Z     Z     = const Refl
invert Z     (S k) = absurd . SIsNotZ . sym
invert (S k) Z     = absurd . SIsNotZ
invert (S k) (S j) = eqSucc k j . invert k j . lemma k j
