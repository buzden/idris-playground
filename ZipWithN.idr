module ZipWithN

import Data.Vect

%default total

namespace FunctionBased

  public export
  FunN : Vect n Type -> Type -> Type
  FunN []      ty = ty
  FunN (x::xs) ty = x -> FunN xs ty

  apFunN : {n : Nat} -> {0 args : Vect n Type} -> Applicative f => f $ FunN args res -> FunN (f <$> args) (f res)
  apFunN {n=Z}   {args=[]}    = id
  apFunN {n=S k} {args=a::as} = \fs, fa => apFunN $ fs <*> fa

  public export
  zipWithN : {n : Nat} -> {0 args : Vect n Type} -> Applicative m => FunN args res -> FunN (m <$> args) (m res)
  zipWithN {n=Z} {args=[]} f = pure f
  zipWithN {n=S k} {args=a::as} f = \xs => apFunN $ f <$> xs
