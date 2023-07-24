import Language.Reflection

%language ElabReflection

data X : Type where
  [noHints]
  A : X
  B : X

%macro %hint
m : Elab X
m = pure A

f : X => Nat
f = 4

failing
  x : Nat
  x = f

%hint
m' : X
m' = A

x : Nat
x = f

f' : Elab X => Nat
f' = 4

x' : Nat
x' = f'
