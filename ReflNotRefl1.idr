module ReflNotRefl1

import Data.Fin
import Data.Vect

import Decidable.Decidable
import Decidable.Equality

public export
data Y = Y1 | Y2 | Y3

public export
data X : Nat -> Type where
  B : Vect n (Maybe Y) -> X n
  W : X n -> (Fin n, Maybe Y) -> X n

public export
ind : Fin n -> X n -> Maybe Y
ind i (B v) = index i v
ind i (W x (j, y)) = if isYes $ decEq i j then y else ind i x

public export
Undef : {n : Nat} -> X n
Undef = B $ replicate n Nothing
