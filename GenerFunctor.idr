-- Credits to Guillaume Allais for the idea

module GenerFunctor

import Control.Category

%default total

------------------
--- Definition ---
------------------

interface
  Category {obj=objC} arrC =>
  Category {obj=objD} arrD =>
  GenFunctor objC objD arrC arrD f | f where
    gmap : {0 a, b : objC} -> arrC a b -> arrD (f a) (f b)

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
