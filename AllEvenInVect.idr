import Data.Nat
import Data.So
import Data.Vect
import Data.Vect.Quantifiers

%default total

first : Vect (S n) a -> a
first (x::_) = x

data IsEven : Nat -> Type where
  EZ : IsEven 0
  SS : IsEven n -> IsEven (2 + n)

multEven : (0 _ : n `GT` 10) => (xs : Vect n Nat) -> All IsEven xs => Vect n Nat

isEven : Nat -> Bool
isEven n = divNatNZ n 2 %search == 0

multEven' : (0 _ : n `GT` 10) => (xs : Vect n Nat) -> All (So . isEven) xs => Vect n Nat
