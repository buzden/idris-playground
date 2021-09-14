module List1T

import Control.Monad.Trans

import Data.List1

%default total

-- primitive implementation, not like in the Haskell's `list-t` package

public export
record List1T m a where
  constructor MkList1T
  runList1T : m (List1 a)

export
Functor m => Functor (List1T m) where
  map f (MkList1T ml) = MkList1T $ map f <$> ml

export
Applicative m => Applicative (List1T m) where
  pure = MkList1T . pure . singleton
  MkList1T ml1 <*> MkList1T ml2 = MkList1T [| ml1 <*> ml2 |]

export
Monad m => Monad (List1T m) where
  MkList1T ml >>= mf = MkList1T $ ml >>= \xs => join <$> traverse (runList1T . mf) xs

export
Foldable m => Foldable (List1T m) where
  foldr f i (MkList1T ml) = foldr (flip $ foldr f) i ml

export
Traversable m => Traversable (List1T m) where
  traverse f (MkList1T ml) = MkList1T <$> traverse (traverse f) ml

export
MonadTrans List1T where
  lift = MkList1T . map singleton
