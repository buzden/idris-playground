module MonadFunctor

import Control.Monad.Error.Either
import Control.Monad.Maybe
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Writer

public export
interface MonadFunctor (0 t : (Type -> Type) -> Type -> Type) where
  liftMap : Monad m => (m a -> m b) -> t m a -> t m b

public export
MonadFunctor (EitherT e) where
  liftMap f (MkEitherT x) = MkEitherT $ x >>= either (pure . Left) (map Right . f . pure)

public export
MonadFunctor MaybeT where
  liftMap f (MkMaybeT x) = MkMaybeT $ x >>= maybe (pure Nothing) (map Just . f . pure)

public export
MonadFunctor (ReaderT r) where
  liftMap f (MkReaderT rr) = MkReaderT $ f . rr

public export
MonadFunctor (RWST r w s) where
  liftMap f (MkRWST rws) = MkRWST $ \r, w, s => rws r w s >>= \(x, ws) => (, ws) <$> f (pure x)

public export
MonadFunctor (StateT s) where
  liftMap f (ST rs) = ST \s => rs s >>= \(r, x) => (r, ) <$> f (pure x)

public export
MonadFunctor (WriterT w) where
  liftMap f (MkWriterT w) = MkWriterT \u => w u >>= \(x, v) => (, v) <$> f (pure x)
