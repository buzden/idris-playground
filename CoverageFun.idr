%default total

failing

  x : Bool -> Nat
  x True = 0

f : Bool -> Bool -> Bool -> Nat
f True  False _     = 1
f False _     True  = 2
f _     True  False = 3
