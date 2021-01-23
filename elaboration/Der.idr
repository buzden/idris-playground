module Der

import Generics.Derive

import Language.Reflection.Derive

%language ElabReflection

data X = A | B Int

%runElab derive "X" [Generic]

record Y (a : Type) (p : a -> Type) where
  constructor MkX
  x : a
  s : p x

-- %runElab derive "Y" [Generic]

Generic (Y a p) [[a, ?dependent]] where
