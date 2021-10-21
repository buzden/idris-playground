module UnboundImplsWhere

import Data.Vect

xs : Nat
xs = 5

-- Having `xs` above gives us a warning as if `xs` in `x` is a parameter.
-- Turning off unbound implicits in the `where` block moves warning away, but leaves implicits to be turned off after where block.

g : Vect n a -> Nat
g xs = x $ lengthCorrect xs where

--  %unbound_implicits off

  x : length xs = n -> Nat
  x _ = 5

f : List a -> Nat
