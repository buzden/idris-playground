module ReflNotRefl1

import Data.Fin
import Data.Vect

import Decidable.Decidable
import Decidable.Equality

public export
data X : Nat -> Type where
  B : (0 n : Nat) -> X n
  W : X n -> (Fin n, Bool) -> X n

public export
ind : Fin n -> X n -> Bool
ind _ (B _) = False
ind i (W x (j, y)) = if isYes $ decEq i j then y else ind i x

prop : ind 3 (B 4 `W` (3, True)) = True
prop = Refl
