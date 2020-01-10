module Proof

%default total
%access export

lemma : (a : Nat) -> (b : Nat) -> S a + S a = S b + S b -> a + a = b + b
lemma a b = rewrite sym $ plusSuccRightSucc a a in
            rewrite sym $ plusSuccRightSucc b b in
            succInjective (a + a) (b + b) . succInjective (S (a + a)) (S (b + b))

invert : (a : Nat) -> (b : Nat) -> (a + a = b + b) -> a = b
invert Z     Z     _ = Refl
invert Z     (S k) p = absurd $ SIsNotZ $ sym p
invert (S k) Z     p = absurd $ SIsNotZ p
invert (S k) (S j) p = eqSucc k j $ invert k j $ lemma k j p
