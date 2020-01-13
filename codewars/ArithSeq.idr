module ArithSeq

%access export
%default total

namespace Preloaded

  %access public export
  %default total

  arithSum : Nat -> Nat
  arithSum Z = Z
  arithSum (S n) = S n + arithSum n

  -- We define our own function for dividing a natural
  -- number by 2.
  -- The existing Idris function divNatNZ
  -- is not a good choice because it is impossible (correct
  -- me if I my wrong) to prove many useful properties of
  -- divNatNZ.
  half : Nat -> Nat
  half (S (S n)) = S (half n)
  half _ = Z

  arithFormula : Nat -> Nat
  arithFormula n = half $ n * (n + 1)

lemma_half_puts_out : (k, x : Nat) -> half ((k + k) + x) = k + half x
lemma_half_puts_out Z     x = Refl
lemma_half_puts_out (S k) x = rewrite plusCommutative k (S k) in
                              rewrite lemma_half_puts_out k x in
                              Refl

arithEq : (n : Nat) -> arithFormula n = arithSum n
arithEq Z     = Refl
arithEq (S k) = rewrite multRightSuccPlus k (k + 1) in
                rewrite plusAssociative (k + 1) k (k * (k + 1)) in
                rewrite plusCommutative k 1 in
                rewrite lemma_half_puts_out k (k * S k) in
                rewrite plusCommutative 1 k in
                rewrite arithEq k in
                Refl
