module Sortings

import Data.Fin
import Data.Vect
import Data.So

%default total

||| Structural inductive rules for prooving that one vector is a permutation of another.
public export
data Permutation : Vect n a -> Vect n a -> Type where
  EmptyPerm  : Permutation [] []
  InsertPerm : {xs : Vect _ a} -> {lys : Vect lm a} -> {rys : Vect rm a}
            -> Permutation xs (lys ++ rys) -> Permutation (x::xs) (rewrite plusSuccRightSucc lm rm in lys ++ x::rys)

public export
data Sorted : {auto ord : Ord a} -> Vect n a -> Type where
  Empty     : Ord a =>                                             Sorted []
  Singleton : Ord a =>                                             Sorted [x]
  Comp      : {x, y : a} -> Sorted {ord} (x::xs) -> So (y <= x) -> Sorted (y::x::xs)

export
soAbsurd : So b -> So (not b) -> Void
soAbsurd sb snb with (sb)
  | Oh = uninhabited snb

export
soNotToNotSo : So (not b) -> Not (So b)
soNotToNotSo = flip soAbsurd

export
isSorted : Ord a => (xs : Vect n a) -> (s : Bool ** if s then Sorted xs else Not (Sorted xs))
isSorted []  = (True ** Empty)
isSorted [_] = (True ** Singleton)
isSorted (y::x::xs) = case choose (y <= x) of
  Left yx => case isSorted (x::xs) of
    (True  ** prf) => (True ** Comp prf yx)
    (False ** prf) => (False ** \(Comp s _) => prf s)
  Right yxNEq => (False ** \(Comp _ yxEq) => soAbsurd yxEq yxNEq)

-- TODO To rewrite isSorted to a `public export sorted : Vect n a -> Bool` function and to a bunch of proof functions
-- TODO   like `So (sorted xs) -> Sorted xs`, `So (not $ sorted xs) -> Not (Sorted xs)`,
-- TODO   `Sorted xs -> So (sorted xs)` and `Not (Sorted xs) -> So (not $ sorted xs)`.

||| Sorting with direct encoding of first-order logic formulae of sortedness properties
export
sortDirect : Ord a => (v : Vect n a) -> (s : Vect n a ** (v `Permutation` s, Sorted s))
sortDirect = ?sortDirect_impl
