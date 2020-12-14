record Four a b c d where
  constructor MkFour
  x : a
  y : b
  z : c
  w : d

firstTwo : Four a b c d -> (a, b)
firstTwo $ MkFour {x, y, _} = (x, y)

record X where
  constructor MkX
  x : Int
  y : Nat
  z : Integer

SomeX : Monad m => m X
SomeX = pure $ MkX {x=5} {y=3} {z=10}

analyzeX : Monad m => m Integer
analyzeX = do
  MkX {y, z, _} <- SomeX
  pure $ z + natToInteger y
