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

analyzeX : Monad m => m Integer
analyzeX = do
  MkX {y, z, _} <- SomeX
  pure $ z + natToInteger y
