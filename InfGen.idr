module InfGen

import Data.Colist
import Data.List.Lazy
import Data.Maybe
import public Data.So

import Language.Reflection

%language ElabReflection

%default total

namespace Gen

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

  data Gen : Type -> Type

  export
  interface AGen a g where
    aGen : g -> Inf (Gen a)

  export
  AGen a (Gen a) where
    aGen = delay

  public export
  data SmallerGen a = Smaller (Inf (Gen a))

  export
  AGen a (SmallerGen a) where
    aGen (Smaller g) = g

  public export %inline %tcinline
  smaller : Inf (Gen a) -> SmallerGen a
  smaller = Smaller

  public export
  data SomeGen : Type -> Type where
    G : AGen a g => g -> SomeGen a

  export
  data Gen : Type -> Type where
    Pure      : a -> Gen a
    Bind      : Gen a -> (a -> Gen b) -> Gen b
    OneOf     : LazyList (Weight Nat, SomeGen a) -> Gen a
    Size      : Gen Nat
    ResetSize : Gen a -> Gen a

  -- NOTE:
  -- Separate `Size` constructor is controversal,
  -- since it's tempting to do, say, `Size >>= \s => frequency [ (1, whatever1), (s, whatever2) ]` which is really ineffective
  -- and can be done with `frequency [ (1, whatever1), (Sized id, whatever2) ]` in the current design.

  export
  oneOf : LazyList (SomeGen a) -> Gen a
  oneOf = OneOf . map (1,)

  export
  frequency : LazyList (Nat, SomeGen a) -> Gen a
  frequency = OneOf . map (mapFst Abs)

  export %tcinline
  frequency' : LazyList (Weight Nat, SomeGen a) -> Gen a
  frequency' = OneOf

  export
  size : Gen Nat
  size = Size

  mapInf : (a -> b) -> Inf a -> Inf b
  mapInf f ia = f ia

  export
  pure : a -> Gen a
  pure = Pure

  export
  Functor Gen where
    map f $ Pure x      = Pure $ f x
    map f $ Bind x g    = Bind x $ map f . g
    map f $ OneOf x     = OneOf $ ?map_oneof -- map (mapSnd $ mapInf $ assert_total map f) x
    map f $ Size        = Size `Bind` Pure . f
    map f $ ResetSize x = ResetSize $ map f x

  export
  Applicative Gen where
    pure = Pure
    nf <*> nb = ?foo_ap

  export
  Monad Gen where
    (>>=) = Bind

nats : Gen Nat
nats = frequency' [ (1, G $ pure Z), (Sized id, G $ smaller $ S <$> nats) ]

nats'' : Gen Nat
nats'' = frequency' [ (1, G $ pure Z), (Sized id, G $ smaller $ S <$> nats) ]

nats''' : Gen Nat
nats''' = impl where
  impl : Gen Nat
  impl = frequency' [ (1, G $ pure Z), (Sized id, G $ smaller $ S <$> nats) ]

effectivelyEmpty : Gen Nat
effectivelyEmpty = oneOf [ G $ smaller effectivelyEmpty ]
