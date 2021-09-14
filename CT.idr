module CT

import Control.Monad.Trans

%default total

-- United container's transformer
-- In fact, it is a `newtype` for `m . c`
-- In fact, all these instances are called `*.Compose` in the standard lib.

public export
record CT (c : Type -> Type) m a where
  constructor MkCT
  runCT : m (c a)

export
Functor c => Functor m => Functor (CT c m) where
  map f (MkCT ml) = MkCT $ map f <$> ml

export
Applicative c => Applicative m => Applicative (CT c m) where
  pure = MkCT . pure . pure
  MkCT ml1 <*> MkCT ml2 = MkCT [| ml1 <*> ml2 |]

export
Applicative c => Alternative m => Alternative (CT c m) where
  empty = MkCT empty
  MkCT ml1 <|> MkCT ml2 = MkCT $ ml1 <|> ml2

export
Monad c => Traversable c => Monad m => Monad (CT c m) where
  MkCT ml >>= mf = MkCT $ ml >>= \xs => join <$> traverse (runCT . mf) xs

export
Foldable c => Foldable m => Foldable (CT c m) where
  foldr f i (MkCT ml) = foldr (flip $ foldr f) i ml

export
Traversable c => Traversable m => Traversable (CT c m) where
  traverse f (MkCT ml) = MkCT <$> traverse (traverse f) ml

export
Applicative c => MonadTrans (CT c) where
  lift = MkCT . map pure
