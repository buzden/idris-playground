import Control.Monad.Either
import Control.Monad.Identity
import Control.Monad.State

import Data.Primitives.Interpolation

%default total

ensureLT : MonadError String m => MonadState Nat m => (w : Nat) -> m ()
ensureLT w = when (not $ w < !get) $ modify S >> throwError "\{w} is not less"

act : MonadError String m => MonadState Nat m => m ()
act = catchError (ensureLT 3) (const $ ensureLT 3)

run1 : Either String Nat
run1 = runIdentity $ runEitherT {m=Identity} $ execStateT 3 act

fii : (Nat, Either String ()) -> Either String Nat
fii (s, e) = mapSnd (const s) e

run2 : Either String Nat
run2 = fii $ runIdentity $ runStateT (the Nat 3) {m=Identity} $ runEitherT {e=String} {m=StateT ? ?} act
