module InfGen

import Data.Colist
import Data.List.Lazy
import public Data.So

import Language.Reflection

%language ElabReflection

%default total

namespace Gen

  public export
  data Weight = Abs Nat | Sized (Nat -> Nat)

  export
  fromInteger : (n : Integer) -> So (n >= 0) => Weight
  fromInteger x = Abs $ fromInteger x

  public export
  data Gen : Type -> Type where
    Pure      : a -> Gen a
    Bind      : Gen a -> (a -> Gen b) -> Gen b
    OneOf     : LazyList (Weight, Inf (Gen a)) -> Gen a
    Size      : Gen Nat
    ResetSize : Gen a -> Gen a
    Smaller   : Inf (Gen a) -> Gen a

  export
  oneOf : LazyList (Inf (Gen a)) -> Gen a
  oneOf = OneOf . map (1,)

  export
  frequency : LazyList (Nat, Inf (Gen a)) -> Gen a
  frequency = OneOf . map (mapFst Abs)

  export
  frequency' : LazyList (Weight, Inf (Gen a)) -> Gen a
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
  smaller' : Inf (Gen a) -> Gen a
  smaller' = Smaller

  export %macro
  smaller : a -> Elab b
  smaller g = do
    g <- quote g
    logTerm "debug" 0 "smaller" g
    check `(smaller' $ delay $ assert_total ~g)

  export
  Functor Gen where
    map f $ Pure x      = Pure $ f x
    map f $ Bind x g    = Bind x $ map f . g
    map f $ OneOf x     = OneOf $ map (mapSnd $ mapInf $ assert_total map f) x
    map f $ Size        = Size `Bind` Pure . f
    map f $ ResetSize x = ResetSize $ map f x
    map f $ Smaller x   = Smaller $ map f x

  export
  Applicative Gen where
    pure = Pure
    nf <*> nb = ?foo

  export
  Monad Gen where
    (>>=) = Bind

nats : Gen Nat
nats = frequency' [ (1, pure Z), (Sized id, smaller $ S <$> nats) ]

nats' : Gen Nat
nats' = smaller nats
