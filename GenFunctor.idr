module GenFunctor

import MonadFunctor

import Control.Monad.Reader
import Control.Monad.Trans

interface GenFunctor n (0 m : Type -> Type) | m where
  gmap : (n a -> n b) -> m a -> m b

Functor m => GenFunctor Prelude.id m where
  gmap = map

f : List Nat -> List Int
f = gmap cast

MonadFunctor t => Monad m => GenFunctor m (t m) where
  gmap = liftMap

[Trans] MonadReader r m => MonadTrans t => GenFunctor m (t m) => Monad (t m) => MonadReader r (t m) where
  ask   = lift ask
  local = gmap . local
