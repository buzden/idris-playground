module Pow

namespace Preloaded
  %access public export
  %default total

  ||| Divides a natural number by 2 and returns
  ||| the quotient and the remainder as a boolean value:
  ||| True = remainder is 1, False = remainder is 0.
  divMod2 : Nat -> (Nat, Bool)
  divMod2 Z     = (Z, False)
  divMod2 (S Z) = (Z, True)
  divMod2 (S (S n)) = case divMod2 n of (q, r) => (S q, r)

  -- The first argument (k) helps Idris to prove
  -- that the function terminates.
  powSqrAux : Nat -> Nat -> Nat -> Nat
  powSqrAux Z _ _ = 1
  powSqrAux _ _ Z = 1
  powSqrAux (S k) b e =
      case divMod2 e of
          (e', False) => powSqrAux k (b * b) e'
          (e', True) => b * powSqrAux k (b * b) e'

  powSqr : Nat -> Nat -> Nat
  powSqr b e = powSqrAux e b e

%access export
%default total

-- The following lemma is useful
divMod2Lemma : (n : Nat) -> n = 2 * fst (divMod2 n) + if snd (divMod2 n) then 1 else 0
divMod2Lemma Z     = Refl
divMod2Lemma (S Z) = Refl
divMod2Lemma (S (S k)) with (divMod2 k) proof eq
    | (q, r) = ?complete_a_proof

powEq : (b, e : Nat) -> powSqr b e = power b e
powEq = ?write_a_proof

