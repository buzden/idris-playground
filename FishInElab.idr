module FishInElab

import Language.Reflection

%default total

%language ElabReflection

x : List String
x = ["a", "b"]

infixl 1 >==>

-- From prelude:
--(>=>) : Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
--(>=>) f g = \x => f x >>= g

(>==>) : Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
(>==>) f g = \x => f x >>= \r => g r

%runElab traverse_ (pure >==> logMsg "debug" 0) x -- works
%runElab traverse_ (pure >=> \s => logMsg "debug" 0 s) x -- works
%runElab traverse_ (pure >=> logMsg "debug" 0) x -- should work, but does not
