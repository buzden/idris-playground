module ZipWithN

import Data.List
import Data.Vect

%default total

public export
interface ZipWithable f where
  zipWith : (a -> b -> c) -> f a -> f b -> f c

public export
ZipWithable List where
  zipWith = List.zipWith

public export
ZipWithable (Vect n) where
  zipWith = Vect.zipWith

namespace FunctionBased

  public export
  FunN : Vect n Type -> Type -> Type
  FunN []      ty = ty
  FunN (x::xs) ty = x -> FunN xs ty

  apFunN : {n : Nat} -> {0 args : Vect n Type} -> ZipWithable f => f $ FunN args res -> FunN (f <$> args) (f res)
  apFunN {n=Z}   {args=[]}    = id
  apFunN {n=S k} {args=a::as} = \fs, fa => apFunN $ zipWith apply fs fa

  public export
  zipWithN : {n : Nat} -> {0 args : Vect n Type} -> (ZipWithable m, Applicative m) => FunN args res -> FunN (m <$> args) (m res)
  zipWithN {n=Z}   {args=[]}    = pure
  zipWithN {n=S k} {args=a::as} = \f, xs => apFunN $ f <$> xs

namespace PseudoTypeclassBased_SearchBoth

  public export
  data FunN : (m : Type -> Type) -> ty -> mty -> Type where
    Constant : FunN m ty (m ty)
    Function : FunN m ty mty -> FunN m (a -> ty) (m a -> mty)

  apFunN : FunN m ty mty => ZipWithable m => m ty -> mty
  apFunN @{Constant}   = id
  apFunN @{Function s} = \fs, fa => apFunN $ zipWith apply fs fa

  public export
  zipWithN : FunN m ty mty => ZipWithable m => Applicative m => ty -> mty
  zipWithN @{Constant}   = pure
  zipWithN @{Function s} = \f, xs => apFunN $ f <$> xs
