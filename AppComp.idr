import Control.Monad.Identity

f1 : Monad m => Int -> m (Either String Int)
f1 5 = pure $ Right 0
f1 _ = pure $ Left "fail 1"

f2 : Monad m => Int -> m (Either String Int)
f2 6 = pure $ Right 0
f2 _ = pure $ Left "fail 2"

c1 : Monad m => m (Either String Int)
c1 = f1 1 *> f2 1

c2 : Monad m => m (Either String Int)
c2 = (f1 1 *> f2 1) @{Applicative.Compose}

-- These checks are meant to be true --

r1 : Bool
r1 = runIdentity c1 == Left "fail 2"

r2 : Bool
r2 = runIdentity c2 == Left "fail 1"
