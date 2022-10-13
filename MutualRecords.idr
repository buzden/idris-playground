import Data.Vect

%default total

mutual

  record X where
    n : Nat
    y : Maybe (x : X ** Y x)

  record Y (x : X) where
    m : Vect x.n Nat

-- but you can't swap definitions inside this mutual blocks,
-- since projections seem to be declared in order, not in `mutual`
