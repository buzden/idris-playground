module MapN

%default total

public export
interface MapN f i o | o where
  mapN : f -> i -> o

public export
MapN Unit a a where
  mapN () = id

public export
MapN (a -> b) a b where
  mapN = apply

public export
MapN c b z => MapN (a -> c) (a, b) z where
  mapN af (x, y) = af x `mapN` y

public export
{0 b, f : a -> Type} -> ({x : a} -> MapN (f x) (b x) z) => MapN ((x : a) -> f x) (x : a ** b x) z where
  mapN af (x ** y) = af x `mapN` y

public export
Functor f => MapN (a -> b) (f a) (f b) where
  mapN = map

public export
Applicative f => MapN (f $ a -> b) (f a) (f b) where
  mapN = (<*>)

public export
Applicative f => MapN m a b => MapN m a (f b) where
  mapN = pure .: mapN

public export
Monad f => MapN s b (f z) => MapN (a -> s) (f a, b) (f z) where
  mapN af (x, y) = map af x >>= (`mapN` y)

public export
Traversable t => Applicative f => MapN s b (f z) => MapN (a -> s) (t a, b) (f . t $ z) where
  mapN af (x, y) = map af x `for` (`mapN` y)

public export
Monad m => MapN (a -> m b) (m a) (m b) where
  mapN = flip (>>=)
