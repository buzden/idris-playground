import Control.Monad.Identity

%default total

-- Validated - an Either with a monoidal error --

public export
data Validated e a = Valid a | Invalid e

public export
(Eq e, Eq a) => Eq (Validated e a) where
  Valid x   == Valid y   = x == y
  Invalid e == Invalid f = e == f
  _ == _ = False

export
(Show e, Show a) => Show (Validated e a) where
  showPrec d $ Valid   x = showCon d "Valid" $ showArg x
  showPrec d $ Invalid e = showCon d "Invalid" $ showArg e

public export
Functor (Validated e) where
  map f $ Valid x   = Valid $ f x
  map _ $ Invalid e = Invalid e

public export
Bifunctor Validated where
  bimap _ s $ Valid x   = Valid   $ s x
  bimap f _ $ Invalid e = Invalid $ f e

-- Composition preserves invalidity
public export
Semigroup e => Applicative (Validated e) where
  pure = Valid

  Valid f    <*> Valid x    = Valid $ f x
  Invalid e1 <*> Invalid e2 = Invalid $ e1 <+> e2
  Invalid e  <*> Valid _    = Invalid e
  Valid _    <*> Invalid e  = Invalid e

-- Composition preserves validity
public export
Semigroup e => Semigroup (Validated e a) where
  l@(Valid _) <+> _           = l
  _           <+> r@(Valid _) = r
  Invalid e1  <+> Invalid e2  = Invalid $ e1 <+> e2

public export
Monoid e => Monoid (Validated e a) where
  neutral = Invalid neutral

-- Composition preserves validity
public export
Monoid e => Alternative (Validated e) where
  empty = neutral
  (<|>) = (<+>)

public export
Foldable (Validated e) where
  foldr op init $ Valid x   = x `op` init
  foldr _  init $ Invalid _ = init

  foldl op init $ Valid x   = init `op` x
  foldl _  init $ Invalid _ = init

  null $ Valid _   = False
  null $ Invalid _ = True

public export
Traversable (Validated e) where
  traverse f $ Valid x   = Valid <$> f x
  traverse _ $ Invalid e = pure $ Invalid e

public export %inline
ValidatedL : Type -> Type -> Type
ValidatedL e a = Validated (List e) a

public export %inline
oneInvalid : e -> Applicative f => Validated (f e) a
oneInvalid x = Invalid $ pure x

public export %inline
fromEither : Either e a -> Validated e a
fromEither $ Right x = Valid x
fromEither $ Left  e = Invalid e

public export %inline
fromEitherL : Either e a -> ValidatedL e a
fromEitherL $ Right x = Valid x
fromEitherL $ Left  e = oneInvalid e

public export %inline
toEither : Validated e a -> Either e a
toEither $ Valid   x = Right x
toEither $ Invalid e = Left e

-- Errorful monadic functions --

f1 : Monad m => Int -> m $ ValidatedL String Int
f1 5 = pure $ pure 0
f1 _ = pure $ oneInvalid "fail 1"

f2 : Monad m => Int -> m $ ValidatedL String Int
f2 6 = pure $ pure 0
f2 _ = pure $ oneInvalid "fail 2"

-- Compositions --

c1 : Monad m => m (ValidatedL String Int)
c1 = f1 1 *> f2 1

c2 : Monad m => m (ValidatedL String Int)
c2 = (f1 1 *> f2 1) @{Applicative.Compose}

-- These checks are meant to be true --

r1 : Bool
r1 = runIdentity c1 == Invalid ["fail 2"]

r2 : Bool
r2 = runIdentity c2 == Invalid ["fail 1", "fail 2"]
