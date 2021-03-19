module ReflNotRefl1

import Data.Fin
import Data.Vect

import Decidable.Decidable
import Decidable.Equality

public export
data X : Nat -> Type where
  B : Vect n Bool -> X n
  W : X n -> (Fin n, Bool) -> X n

public export
ind : Fin n -> X n -> Bool
ind i (B v) = index i v
ind i (W x (j, y)) = if isYes $ decEq i j then y else ind i x

public export
Undef : {n : Nat} -> X n
Undef = B $ replicate n False

prop : ind 3 (Undef {n=4} `W` (3, True)) = True
prop = Refl
