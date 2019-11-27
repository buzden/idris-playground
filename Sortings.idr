module Sortings

import Data.Fin
import Data.Vect
import Data.So

%default total

||| Structural inductive rules for prooving that one vector is a permutation of another.
data Permutation : Vect n a -> Vect n a -> Type where
  EmptyPerm  : Permutation [] []
  InsertPerm : {lys : Vect lm a} -> {rys : Vect rm a}
            -> Permutation xs (lys ++ rys) -> Permutation (x::xs) (rewrite plusSuccRightSucc lm rm in lys ++ x::rys)

data Sorted : {auto ord : Ord a} -> Vect n a -> Type where
  Empty     : Ord a =>                                             Sorted []
  Singleton : Ord a =>                                             Sorted [x]
  Comp      : {x, y : a} -> Sorted {ord} (x::xs) -> So (y <= x) -> Sorted (y::x::xs)

soAbsurd : So b -> So (not b) -> Void
soAbsurd sb snb with (sb)
  | Oh = uninhabited snb

soNotToNotSo : So (not b) -> Not (So b)
soNotToNotSo = flip soAbsurd

isSorted : Ord a => (xs : Vect n a) -> (s : Bool ** if s then Sorted xs else Not (Sorted xs))
isSorted []  = (True ** Empty)
isSorted [_] = (True ** Singleton)
isSorted (y::x::xs) = case choose (y <= x) of
  Left yx => case isSorted (x::xs) of
    (True  ** prf) => (True ** Comp prf yx)
    (False ** prf) => (False ** \(Comp s _) => prf s)
  Right yxNEq => (False ** \(Comp _ yxEq) => soAbsurd yxEq yxNEq)

||| Sorting with direct encoding of first-order logic formulae of sortedness properties
sortDirect : Ord a => (v : Vect n a) -> (s : Vect n a ** (v `Permutation` s, Sorted s))
sortDirect = ?sortDirect_impl
