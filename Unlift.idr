import Control.Monad.Either
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

record Unlift (0 t : (Type -> Type) -> Type -> Type) where
  constructor MkUnlift
  unlifter : forall n, a. Monad n => t n a -> n a

-- inlining `Unlift` type to its the only field make the code to not to typecheck somewhy O_O

interface MonadTransUnlift t where
  askUnlift : Monad m => t m $ Unlift t

MonadTransUnlift (ReaderT r) where
  askUnlift = MkReaderT $ \r => pure $ MkUnlift $ runReaderT r

-- those below are somewhat bad...

MonadTransUnlift (StateT s) where
  askUnlift = ST $ \s => pure (s, MkUnlift $ evalStateT s)

Monoid w => MonadTransUnlift (WriterT w) where
  askUnlift = MkWriterT $ \w => pure (MkUnlift $ map fst . runWriterT, w)

MonadTransUnlift (EitherT e) where
  askUnlift = MkEitherT $ pure $ Right $ MkUnlift $ ?foo
