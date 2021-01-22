module ZipWithN

import Data.Vect

%default total

namespace FunctionBased

  public export
  FunN : Vect n Type -> Type -> Type
  FunN []      ty = ty
  FunN (x::xs) ty = x -> FunN xs ty

  mapFunN : {n : Nat} -> {0 args : Vect n Type} -> (res1 -> res2) -> FunN args res1 -> FunN args res2
  mapFunN {n=Z}   {args=[]}    f x  = f x
  mapFunN {n=S k} {args=a::as} f fs = mapFunN f . fs

  sequenceFunN : {n : Nat} -> {0 args : Vect n Type} -> Functor f => f $ FunN args res -> FunN args $ f res
  sequenceFunN {n=Z}   {args=[]}    = id
  sequenceFunN {n=S k} {args=a::as} = \xs, x => sequenceFunN $ (\f => f x) <$> xs

  public export
  zipWithN : {n : Nat} -> {0 args : Vect n Type} -> Monad f => FunN args res -> FunN (f <$> args) (f res)
  zipWithN {n=Z} {args=[]} f = pure f
  zipWithN {n=S k} {args=a::as} f = \xs => mapFunN join $ sequenceFunN $ zipWithN <$> f <$> xs

  constFunN : {n : Nat} -> {0 args : Vect n Type} -> r -> FunN args r
  constFunN {n=Z}   {args=[]}    = id
  constFunN {n=S k} {args=a::as} = const . constFunN
