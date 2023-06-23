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

  export
  data Gen : Type -> Type where
    Pure      : a -> Gen a
    Bind      : Gen a -> (a -> Gen b) -> Gen b
    OneOf     : LazyList (Weight Nat, Inf (Gen a)) -> Gen a
    Size      : Gen Nat
    ResetSize : Gen a -> Gen a
    Smaller   : Inf (Gen a) -> Gen a

  -- NOTE:
  -- Separate `Size` constructor is controversal,
  -- since it's tempting to do, say, `Size >>= \s => frequency [ (1, whatever1), (s, whatever2) ]` which is really ineffective
  -- and can be done with `frequency [ (1, whatever1), (Sized id, whatever2) ]` in the current design.

  export
  oneOf : LazyList (Inf (Gen a)) -> Gen a
  oneOf = OneOf . map (1,)

  export
  frequency : LazyList (Nat, Inf (Gen a)) -> Gen a
  frequency = OneOf . map (mapFst Abs)

  export
  frequency' : LazyList (Weight Nat, Inf (Gen a)) -> Gen a
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

  export
  interface SomeGen a g where
    fromGen : Gen a -> g

  export
  SomeGen a (Gen a) where
    fromGen = id

  export
  SomeGen a (Inf (Gen a)) where
    fromGen = delay

  export %macro %inline
  smaller : SomeGen a b => Inf (Gen a) -> Elab b
  smaller g = do

    -- check that `g` typechecks as a separate total function
    -- commented out because of the compiler's issue https://github.com/idris-lang/Idris2/issues/2993
--    qg <- quote g -- this will require `public export` on `data Gen` due to too deep quotation
--    name <- genSym "smcheck"
--    ty <- fromMaybe `(InfGen.Gen.Gen ?) <$> goal
--    let claim = IClaim EmptyFC MW Private [Totality Total] $ MkTy EmptyFC EmptyFC name ty
--    let body = IDef EmptyFC name $ pure $ PatClause EmptyFC (IVar EmptyFC name) qg
--    let ns = INamespace EmptyFC (MkNS [show !(genSym "Sm"), "SmChecks"]) [claim, body]
--    declare [ns] <|> failAt (getFC qg) "Can't prove that generator under `smaller` is total"

    -- form the resulting wrapping expression
    pure $ fromGen $ delay $ smaller' $ assert_total g

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
    nf <*> nb = ?foo_ap

  export
  Monad Gen where
    (>>=) = Bind

nats : Gen Nat
nats = frequency' [ (1, pure Z), (Sized id, smaller $ S <$> nats) ]

nats'' : Gen Nat
nats'' = frequency' [ (1, pure Z), (Sized id, smaller $ S <$> nats) ]

nats''' : Gen Nat
nats''' = impl where
  impl : Gen Nat
  impl = frequency' [ (1, pure Z), (Sized id, smaller $ S <$> nats) ]

nats' : Gen Nat
nats' = smaller nats

failing "Can't" -- can be also "Mismatch between `Gen Nat` and `Nat`"
  na : Nat
  na = smaller nats

covering
natsBad : Gen Nat
natsBad = oneOf [ natsBad ]

natsVeryBad : Gen Nat
natsVeryBad = smaller natsBad

effectivelyEmpty : Gen Nat
effectivelyEmpty = smaller effectivelyEmpty
