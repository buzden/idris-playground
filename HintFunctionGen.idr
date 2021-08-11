module HintFunctionGen

export
record Gen a where
  constructor MkGen
  cont : List a

export
Functor Gen where
  map f (MkGen xs) = MkGen $ f <$> xs

export
Applicative Gen where
  pure = MkGen . pure
  MkGen xs <*> MkGen ys = MkGen $ xs <*> ys

export
Alternative Gen where
  empty = MkGen empty
  MkGen xs <|> mys = MkGen $ xs <|> mys.cont

export
Monad Gen where
  MkGen xs >>= f = MkGen $ xs >>= cont . f

export
Show a => Show (Gen a) where
  show = ("gen " ++) . show . cont
