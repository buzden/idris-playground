module InfGen

import Data.Colist
import Data.List.Lazy
import Data.Maybe
import public Data.So

import Language.Reflection

%language ElabReflection

%default total

namespace Weight

  public export
  data Weight sz = Abs sz | Sized (Nat -> sz)

  export
  fromInteger : (n : Integer) -> (0 _ : So $ n >= 0) => Weight Nat
  fromInteger x = Abs $ fromInteger x

  export
  Semigroup sz => Semigroup (Weight sz) where
    Abs x   <+> Abs y   = Abs   $ x <+> y
    Abs x   <+> Sized f = Sized $ (x <+>) . f
    Sized f <+> Abs y   = Sized $ (<+> y) . f
    Sized f <+> Sized g = Sized $ \w => f w <+> g w

  export
  Monoid sz => Monoid (Weight sz) where
    neutral = Abs neutral

namespace Gen

  export
  data Gen : Type -> Type

  data Gen : Type -> Type where
    Pure      : a -> Gen a
    Bind      : Gen a -> (a -> Gen b) -> Gen b
    OneOf     : LazyList (Weight Nat, Gen a) -> Gen a
    Size      : Gen Nat
    Smaller   : Inf (Gen a) -> Gen a
    ResetSize : Gen a -> Gen a

  -- NOTE:
  -- Separate `Size` constructor is controversal,
  -- since it's tempting to do, say, `Size >>= \s => frequency [ (1, whatever1), (s, whatever2) ]` which is really ineffective
  -- and can be done with `frequency [ (1, whatever1), (Sized id, whatever2) ]` in the current design.

  export %inline
  smaller' : Inf (Gen a) -> Gen a
  smaller' = Smaller

  public export %inline %tcinline
  smaller : Inf (Gen a) -> Gen a
  smaller x = assert_total (smaller' x)

  export %inline
  resetSize : Gen a -> Gen a
  resetSize = ResetSize

  export %inline
  oneOf : LazyList (Gen a) -> Gen a
  oneOf = OneOf . map (1,)

  export %inline
  frequency : LazyList (Nat, Gen a) -> Gen a
  frequency = OneOf . map (mapFst Abs)

  export %inline
  frequency' : LazyList (Weight Nat, Gen a) -> Gen a
  frequency' = OneOf

  export
  size : Gen Nat
  size = Size

  export %inline
  pure : a -> Gen a
  pure = Pure

  export
  Functor Gen where
    map f $ Pure x      = Pure $ f x
    map f $ Bind x g    = Bind x $ map f . g
    map f $ OneOf x     = OneOf $ map (map (assert_total map f)) x
    map f $ Size        = Size `Bind` Pure . f
    map f $ Smaller x   = Smaller $ map f x
    map f $ ResetSize x = ResetSize $ map f x

  export
  Applicative Gen where
    pure = Gen.pure
    nf <*> nb = Bind nf (<$> nb)

  export
  Monad Gen where
    (>>=) = Bind

  export
  unGen : Monad m => (any : forall a. (n : LazyList a) -> m $ Maybe a) -> (size : Nat) -> Gen a -> m $ Maybe a
  unGen any initSize = go initSize where
    go : forall a. (size : Nat) -> Gen a -> m $ Maybe a
    go _     $ Pure x      = pure $ pure x
    go size  $ Bind x f    = (go size x >>= go size . f) @{Compose}
    go size  $ OneOf x     = (any x >>= assert_total go size . snd) @{Compose}
    go size  $ Size        = pure $ pure size
    go Z     $ Smaller x   = pure Nothing
    go (S s) $ Smaller x   = go s x
    go _     $ ResetSize x = assert_total go initSize x -- I don't know why it does not total-check without `assert_total` here

nats : Gen Nat
nats = frequency' [ (1, pure Z), (Sized id, smaller $ S <$> nats) ]

nats'' : Gen Nat
nats'' = frequency' [ (1, pure Z), (Sized id, smaller $ S <$> nats) ]

nats''' : Gen Nat
nats''' = impl where
  impl : Gen Nat
  impl = frequency' [ (1, pure Z), (Sized id, smaller $ S <$> nats) ]

effectivelyEmpty : Gen Nat
effectivelyEmpty = oneOf [ smaller effectivelyEmpty ]

failing "looping is not total"
  looping : Gen Nat
  looping = resetSize looping

failing "looping is not total"
  looping : Gen Nat
  looping = oneOf [ resetSize looping ]
