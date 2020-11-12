module SqEq0

sqeq0 : (a, b : Nat) -> a*a + b*b = 0 -> (a = 0, b = 0)
sqeq0 0 0 Refl = (Refl, Refl)
