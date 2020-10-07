module InterfaceWith0s

interface Lala (a : Type) where
  f : a -> a
  z : a -> a -> Bool
  0 prop : (x : a) -> z (f x) x = True
