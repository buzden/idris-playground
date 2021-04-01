module MonadFunctor

import Control.Monad.Error.Either
import Control.Monad.Maybe
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Writer

public export
interface MonadFunctor (0 t : (Type -> Type) -> Type -> Type) where
  liftMap : (forall a. m a -> n a) -> t m a -> t n a

public export
MonadFunctor (EitherT e) where
  liftMap f (MkEitherT x) = MkEitherT $ f x

public export
MonadFunctor MaybeT where
  liftMap f (MkMaybeT x) = MkMaybeT $ f x

public export
MonadFunctor (ReaderT r) where
  liftMap f (MkReaderT rr) = MkReaderT $ f . rr

public export
MonadFunctor (RWST r w s) where
  liftMap f (MkRWST rws) = MkRWST $ (f .) .: rws

public export
MonadFunctor (StateT s) where
  liftMap f (ST rs) = ST $ f . rs

public export
MonadFunctor (WriterT w) where
  liftMap f (MkWriterT w) = MkWriterT $ f . w
