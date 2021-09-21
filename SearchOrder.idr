module SearchOrder

%default total

interface De where
  f : Nat -> Nat

De where
  f = (+1)

g : De => Nat -> Nat
g x = f (x + 1)

[R] De where
  f = (+2)

ch1 : g 4 = 6
ch1 = Refl

-- Check that local is preferred to the global
ch2 : g @{R} 4 = 7
ch2 = Refl
