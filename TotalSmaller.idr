%default total

data T = A | B

fWF : T -> Nat
fWF A = S Z
fWF B = Z

-- Provably total variant of function
-- ```
-- f : T -> Bool
-- f A = f B
-- f B = True
-- ```
f : T -> Bool
f x with (fWF x) proof p
  f A | S Z = (f B | Z) {p = Refl}
  f B | Z   = True
