-- Copyright 2023-2025 Denis Buzdalov
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.
--
module InfGen

import Control.Monad.Random

import Data.Colist
import Data.List.Lazy
import Data.Maybe
import Data.Nat
import public Data.So
import Data.These

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

  public export
  weight : (size : Nat) -> Weight sz -> sz
  weight _ (Abs x)   = x
  weight w (Sized f) = f w

namespace Depth

  public export
  data Depth = Infinite | Finite Nat

  public export
  Eq Depth where
    Infinite == Infinite = True
    Finite l == Finite r = l == r
    _ == _ = False

  public export
  Ord Depth where
    compare Infinite Infinite     = EQ
    compare Infinite (Finite _)   = GT
    compare (Finite _) Infinite   = LT
    compare (Finite l) (Finite r) = compare l r

  public export
  next : Depth -> Depth
  next Infinite   = Infinite
  next $ Finite n = Finite $ S n

  public export
  maximum : Depth -> Depth -> Depth
  maximum Infinite _ = Infinite
  maximum _ Infinite = Infinite
  maximum (Finite n) (Finite m) = Finite $ maximum n m

  public export
  data LTE : Depth -> Depth -> Type where
    LTE_I : LTE d Infinite
    LTE_F : LTE n m -> LTE (Finite n) (Finite m)

  export
  Reflexive Depth LTE where
    reflexive {x=Infinite} = LTE_I
    reflexive {x=Finite k} = LTE_F reflexive

  export
  Transitive Depth LTE where
    transitive LTE_I     LTE_I     = LTE_I
    transitive (LTE_F l) LTE_I     = LTE_I
    transitive (LTE_F l) (LTE_F r) = LTE_F $ transitive l r

  public export
  splitMaxN : {l, r : Nat} -> maximum l r `LTE` n -> (l `LTE` n, r `LTE` n)
  splitMaxN {l=Z} LTEZero = (LTEZero, LTEZero)
  splitMaxN {l=Z} {r=S r} (LTESucc x) = (LTEZero, LTESucc x)
  splitMaxN {l=S l} {r=Z} x = (x, LTEZero)
  splitMaxN {l=S l} {r=S r} (LTESucc x) = mapFst LTESucc $ mapSnd LTESucc $ splitMaxN x

  public export
  splitMinLTE : {l, r, n : Nat} -> (0 _ : minimum l r `LTE` n) -> These (l `LTE` n) (r `LTE` n)
  splitMinLTE {l=Z}   {r=Z  } {n}     _           = Both LTEZero LTEZero
  splitMinLTE {l=Z}   {r=S r} {n=Z  } LTEZero     = This LTEZero
  splitMinLTE {l=Z}   {r=S r} {n=S n} LTEZero     = bimap (\LTEZero => LTEZero) LTESucc $ splitMinLTE {l=Z} {r} {n} LTEZero
  splitMinLTE {l=S l} {r=Z  } {n=Z  } LTEZero     = That LTEZero
  splitMinLTE {l=S l} {r=Z  } {n=S n} LTEZero     = bimap LTESucc (\LTEZero => LTEZero) $ splitMinLTE {l} {r=Z} {n} $ rewrite minimumCommutative l Z in LTEZero
  splitMinLTE {l=S l} {r=S r} {n=S n} $ LTESucc x = bimap LTESucc LTESucc $ splitMinLTE x

  public export
  splitMax : {dl, dr : Depth} -> maximum dl dr `LTE` d -> (dl `LTE` d, dr `LTE` d)
  splitMax {dl=Infinite} {d=Infinite} LTE_I = (LTE_I, LTE_I)
  splitMax {dr=Infinite} {d=Infinite} LTE_I = (LTE_I, LTE_I)
  splitMax {dl=Finite n} {dr=Finite m} {d=Infinite} LTE_I = (LTE_I, LTE_I)
  splitMax {dl=Finite n} {dr=Finite m} {d=Finite k} $ LTE_F slte = mapFst LTE_F $ mapSnd LTE_F $ splitMaxN slte

  export %hint
  unFiniteLTE : LTE (Finite l) (Finite r) => LTE l r
  unFiniteLTE @{LTE_F x} = x

  export
  0 unSLTE : LTE (next l) (Finite $ S r) => LTE l (Finite r)
  unSLTE {l=Finite k} @{LTE_F $ LTESucc x} = LTE_F x

  export
  0 weakenNextLTE : LTE (next l) r => LTE l r
  weakenNextLTE {l=Finite k} @{LTE_F x} = LTE_F $ lteSuccLeft x
  weakenNextLTE {l=Infinite} @{lte}     = lte

  export
  0 U_N_0 : Uninhabited (next d `LTE` Finite 0)
  U_N_0 = MkUninhabited u where
    u : forall d. Not $ next d `LTE` Finite 0
    u lte {d} with 0 (next d) proof nextd
      u lte         {d=Infinite} | Finite _     = case nextd of Refl impossible
      u (LTE_F lte) {d=Finite y} | Finite (S x) = case lte of _ impossible

namespace Gen

  data Gen : (minDepth : Depth) -> Type -> Type

  export
  data GenAlts : (empty : Bool) -> Type -> Type where
    None : GenAlts True a
    More : Weight Nat -> {depth : _} -> Gen (Finite depth) a -> Lazy (GenAlts e a) -> GenAlts False a

  namespace GenAltsSyntax
    public export %inline
    Nil : GenAlts True a
    Nil = None

    public export %inline
    (::) : {depth : _} -> (Weight Nat, Gen (Finite depth) a) -> Lazy (GenAlts e a) -> GenAlts False a
    (::) (w, g) = More w g

  public export
  minDepth : GenAlts False a -> Nat
  minDepth $ More _ {depth} _ $ Delay None         = depth
  minDepth $ More _ {depth} _ $ Delay xs@(More {}) = minimum depth $ minDepth xs

  export
  data Gen : (minDepth : Depth) -> Type -> Type where
    Empty     : Gen Infinite a
    Pure      : a -> Gen (Finite 0) a
    Bind      : Gen dl a -> (a -> Gen dr b) -> Gen (maximum dl dr) b
    OneOf     : (alts : GenAlts False a) -> Gen (Finite $ minDepth alts) a
    Size      : Gen (Finite 0) Nat
    Smaller   : Inf (Gen d a) -> Gen (next d) a
    ResetSize : Gen d a -> Gen d a -- I doubt on correctness of depth rules here

  -- NOTE:
  -- Separate `Size` constructor is controversal,
  -- since it's tempting to do, say, `Size >>= \s => frequency [ (1, whatever1), (s, whatever2) ]` which is really ineffective
  -- and can be done with `frequency [ (1, whatever1), (Sized id, whatever2) ]` in the current design.

  export %inline
  smaller' : Inf (Gen d a) -> Gen (next d) a
  smaller' = Smaller

  public export %inline %tcinline
  smaller : Inf (Gen d a) -> Gen (next d) a
  smaller x = assert_total (smaller' x)

  export %inline
  resetSize : Gen d a -> Gen d a
  resetSize = ResetSize

  export %inline
  frequency' : (alts : GenAlts False a) -> Gen (Finite $ minDepth alts) a
  frequency' = OneOf

--  export %inline
--  oneOf : LazyList (Gen d a) -> Gen d a
--  oneOf = frequency' . map (1,)

--  export %inline
--  frequency : LazyList (Nat, Gen d a) -> Gen d a
--  frequency = frequency' . map (mapFst Abs)

  export
  size : Gen (Finite 0) Nat
  size = Size

  export %inline
  pure : a -> Gen (Finite 0) a
  pure = Pure

  mutual
    export
    Functor (GenAlts e) where
      map f None = None
      map f (More x y z) = More x (map f y) (map f z)

    export
    minDepth_max_invariant : (f : a -> b) -> (alts : GenAlts False a) -> minDepth (map f alts) = minDepth alts
    minDepth_max_invariant f $ More x y $ Delay None        = Refl
    minDepth_max_invariant f $ More x y $ Delay z@(More {}) = rewrite minDepth_max_invariant f z in Refl

    export
    Functor (Gen d) where
      map f Empty         = Empty
      map f $ Pure x      = Pure $ f x
      map f $ Bind x g    = Bind x $ map f . g
      map f $ OneOf x     = rewrite sym $ minDepth_max_invariant f x in OneOf $ assert_total map f x
      map f $ Size        = Size `Bind` Pure . f
      map f $ Smaller x   = Smaller $ map f x
      map f $ ResetSize x = ResetSize $ map f x

--  export
--  Applicative Gen where
--    pure = Gen.pure
--    nf <*> nb = Bind nf (<$> nb)
--
--  export
--  Monad Gen where
--    (>>=) = Bind

  filterAlts' : (size : Nat) -> GenAlts False a -> List1 (Nat, (d ** Gen d a))

  export
  unGen : Monad m => (any : forall a. List1 (Nat, a) -> m a) -> (size : Nat) -> Gen depth a -> m $ Maybe a
  unGen any initSize = go initSize where
    go : forall a, depth. (size : Nat) -> Gen depth a -> m $ Maybe a
    go _     Empty         = pure Nothing
    go _     $ Pure x      = pure $ pure x
    go size  $ Bind x f    = (go size x >>= go size . f) @{Compose}
    go size  $ OneOf x     = any (filterAlts' size x) >>= \(_ ** x) => assert_total go size x
    go size  $ Size        = pure $ pure size
    go Z     $ Smaller x   = pure Nothing
    go (S s) $ Smaller x   = go s x
    go _     $ ResetSize x = assert_total go initSize x -- I don't know why it does not total-check without `assert_total` here

  record FilteredGen size a where
    constructor MkFilteredGen
    0 actualDepth : ?
    0 depthBound : actualDepth `LTE` size
    filteredGen : Gen (Finite actualDepth) a

  covering
  filterAlts : (size : Nat) -> (alts : GenAlts False a) -> (0 _ : minDepth alts `LTE` size) => List1 (Nat, FilteredGen size a)
  filterAlts size @{slt} $ More w g $ Delay None         = (weight size w, MkFilteredGen _ %search g) ::: []
  filterAlts size @{slt} $ More w g $ Delay (More x y z) = case splitMinLTE slt of
    This l   => (weight size w, MkFilteredGen _ l g) ::: []
    That r   => filterAlts size $ More x y z
    Both l r => (weight size w, MkFilteredGen _ l g) ::: forget (filterAlts size $ More x y z)

  export
  unGen1 : Monad m => (any : forall a. List1 (Nat, a) -> m a) -> (size : Nat) -> (0 _ : depth `LTE` Finite size) => Gen depth a -> m a
  unGen1 any {depth=initDepth} initSize = go initSize @{reflexive} where
    go : forall a, depth. (size : Nat) -> (0 sizeI : size `LTE` initSize) => (0 depthS : depth `LTE` Finite size) => Gen depth a -> m a
    go _     $ Pure x      = pure x
    go size  $ Bind x f    = let 0 dp = splitMax depthS in go size x >>= go size . f
    go size  $ OneOf x     = any (filterAlts size x) >>= \(MkFilteredGen xd xdprf x) => assert_total go size x
    go size  $ Size        = pure size
    go Z     $ Smaller _   = void $ absurd @{U_N_0} depthS -- WTF, why can't it find this by itself?
    go (S s) $ Smaller x   = go @{lteSuccLeft %search} @{unSLTE} s x
    go _     $ ResetSize x = assert_total go @{reflexive} {depthS = transitive depthS $ LTE_F sizeI} initSize x
                             -- I don't know why it does not total-check without `assert_total` here
namespace Random

  pickWeighted : Nat -> List1 (Nat, a) -> a
  pickWeighted _ (x     :::[]        ) = snd x
  pickWeighted n ((w, x):::xs@(y::ys)) = if n < w then x else pickWeighted (n `minus` w) (assert_smaller xs $ y:::ys)
                                                                                     -- `assert_smaller` should be unneeded here

  export
  any : MonadRandom m => List1 (Nat, a) -> m a
  any xs = getRandomR (0, sum $ fst <$> xs) <&> \n => pickWeighted n xs

nats : Gen (Finite 0) Nat
nats = frequency' [ (1, pure Z), (Sized id, smaller $ S <$> nats) ]

nats'' : Gen (Finite 0) Nat
nats'' = frequency' [ (1, pure Z), (Sized id, smaller $ S <$> nats) ]

nats''' : Gen (Finite 0) Nat
nats''' = impl where
  impl : Gen (Finite 0) Nat
  impl = frequency' [ (1, pure Z), (Sized id, smaller $ S <$> nats) ]

effectivelyEmpty : Gen Infinite Nat
--effectivelyEmpty = oneOf [ smaller effectivelyEmpty ]
effectivelyEmpty = smaller effectivelyEmpty

failing "looping is not total"
  looping : Gen Infinite Nat
  looping = resetSize looping

--failing "looping is not total"
--  looping : Gen Infinite Nat
--  looping = oneOf [ resetSize looping ]

export
main : IO ()
main = printLn =<< for [Z..100] (const $ evalRandomIO $ unGen1 any 40 nats)
