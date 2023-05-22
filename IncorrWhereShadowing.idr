module IncorrWhereShadowing

import Data.Fin
import Data.Vect
import Data.Vect.AtIndex

import Decidable.Equality

%default total

genAtIndex' : DecEq a => (n : Nat) -> (f : Fin n) -> (m : a) -> (v : Vect n a) -> Maybe $ AtIndex f v m
genAtIndex' n' f m v = genHere n' f m v
  where
    genHere : (n : Nat) -> (f : Fin n) -> (m : a) -> (v : Vect n a) -> Maybe $ AtIndex f v m
    genHere (S n) FZ x (x0 :: xs) with (decEq x x0)
      genHere (S n) FZ x (x :: xs)  | Yes Refl = pure Here
      genHere (S n) FZ x (x0 :: xs) | No _ = empty
    genHere _ _ _ _ = empty

failing "Mismatch between: n and n"

  genAtIndex : DecEq a => (n : Nat) -> (f : Fin n) -> (m : a) -> (v : Vect n a) -> Maybe $ AtIndex f v m
  genAtIndex n f m v = genHere n f m v
    where
      genHere : (n : Nat) -> (f : Fin n) -> (m : a) -> (v : Vect n a) -> Maybe $ AtIndex f v m
      genHere (S n) FZ x (x0 :: xs) with (decEq x x0)
        genHere (S n) FZ x (x :: xs)  | Yes Refl = pure Here
        genHere (S n) FZ x (x0 :: xs) | No _ = empty
      genHere _ _ _ _ = empty
