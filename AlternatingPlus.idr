module AlternatingPlus

import Data.Vect

%default total

public export
modulo : {k : _} -> Nat -> Fin $ S k
modulo Z     = FZ
modulo (S n) = finS $ modulo n

public export
data AltLi : Nat -> Vect (S tysn) Type -> Type where
  Nil  : AltLi Z tys
  (::) : {tysn : _} -> {0 tys : Vect (S tysn) _} -> modulo n `index` tys -> AltLi n tys -> AltLi (S n) tys

e_1_1 : AltLi 1 [Nat]
e_1_1 = [5]

--e_4_1 : AltLi 4 [Nat]
--e_4_1 = [1, 2, 3, 4]

e_1_3 : AltLi 1 [Nat, String, Char]
e_1_3 = [5]

--e_4_3 : AltLi 4 [Nat, String, Char]
--e_4_3 = [5, "five", 'k', 6]
