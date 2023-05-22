module IncorrWhereShadowing

import Data.Vect

%default total

failing "Mismatch between: n and n"

  outer : (n : Nat) -> (v : Vect n a) -> Unit
  outer n v = inner n v where
    inner : (n : Nat) -> (v : Vect n a) -> Unit
    inner n xs with (())
      inner n xs | () = ()
