module MonadTransUniv

import public MonadFunctor

import Control.Monad.Error.Interface
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Writer

namespace Reader

  public export %inline
  [Trans] MonadReader r m => MonadTrans t => MonadFunctor t => Monad (t m) => MonadReader r (t m) where
    ask   = lift ask
    local = liftMap . local

namespace State

  public export %inline
  [Trans] MonadState s m => MonadTrans t => Monad (t m) => MonadState s (t m) where
    get   = lift get
    put   = lift . put
    state = lift . state

namespace Writer

  public export %inline
  [Trans] MonadWriter r m => MonadTrans t => MonadFunctor t => Monad (t m) => MonadWriter r (t m) where
    writer = lift . writer
    tell   = lift . tell
    listen = liftMap listen
    pass   = liftMap pass
