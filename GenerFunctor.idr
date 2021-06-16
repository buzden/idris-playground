-- Credits to Guillaume Allais for the idea

module GenerFunctor

import Control.Category

import Control.Monad.Reader
import Control.Monad.Trans

%default total

------------------
--- Definition ---
------------------

interface
  Category {obj=objC} arrC =>
  Category {obj=objD} arrD =>
  GenFunctor objC objD arrC arrD f | f where
  --GenFunctor objC objD (0 arrC : objC -> objC -> Type) (0 arrD : objD -> objD -> Type) (0 f : objC -> objD) | f where
    gmap : {0 a, b : objC} -> arrC a b -> arrD (f a) (f b)

  -- Didn't manage to get rid of explicit `objC`, `objD`, `arrC` and `arrD` parameters.

-----------------------------
--- Auxiliary definitions ---
-----------------------------

%inline
Fun : Type -> Type -> Type
Fun = \a, b => a -> b

%inline
WrFun : (Type -> Type) -> Type -> Type -> Type
WrFun f = \a, b => f a -> f b

{0 m : Type -> Type} -> Category (WrFun m) where
  id = id
  (.) = (.)

------------------------------------
--- `GenFunctor` is more general ---
------------------------------------

--interface Functor f where
--  map : (a -> b) -> f a -> f b

Functor m => GenFunctor Type Type Fun Fun m where
  gmap = map

Functor m => GenFunctor Type Type Fun (WrFun m) Prelude.id where
  gmap = map

-------------

interface MonadLiftMap (0 t : (Type -> Type) -> Type -> Type) where
  liftMap : Monad m => (m a -> m b) -> t m a -> t m b

MonadLiftMap t => Monad m => GenFunctor Type Type (WrFun m) Fun (t m) where
  gmap = liftMap

MonadLiftMap t => Monad m => GenFunctor Type Type (WrFun m) (WrFun $ t m) Prelude.id where
  gmap = liftMap

-------------

interface PrevGenFunctor n (0 m : Type -> Type) | m where
  pgmap : (n a -> n b) -> m a -> m b

PrevGenFunctor n m => GenFunctor Type Type (WrFun n) Fun m where
  gmap = pgmap

PrevGenFunctor n m => GenFunctor Type Type (WrFun n) (WrFun m) Prelude.id where
  gmap = pgmap

-------------
--- Usage ---
-------------

-- All those `gmap {f=...}` work only when we have `GenFunctor ... f | f where` functional dependency

ns2is : List Nat -> List Int
ns2is = gmap {f=List} cast

[Trans] MonadReader r m => MonadTrans t => GenFunctor Type Type (WrFun m) Fun (t m) => Monad (t m) => MonadReader r (t m) where
  ask   = lift ask
  local = gmap {f=t m} . local
