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

public export
sorted : Ord a => Vect n a -> Bool
sorted [] = True
sorted [_] = True
sorted (y::x::xs) = (y <= x) && sorted (x::xs)

namespace SortedProperties
  export
  valueToType : Ord a => {xs : Vect n a} -> So (sorted xs) -> Sorted xs
  valueToType = ?valueToType_impl

  export
  notValueToNotType : Ord a => {xs : Vect n a} -> So (not $ sorted xs) -> Not (Sorted xs)
  notValueToNotType = ?notValueToNotType_impl

  export
  typeToValue : Ord a => Sorted xs -> So (sorted xs)
  typeToValue = ?typeToValue_impl

  export
  notTypeToNotValue : Ord a => Not (Sorted xs) -> So (not $ sorted xs)
  notTypeToNotValue = ?notTypeToNotValue_impl

||| Sorting with direct encoding of first-order logic formulae of sortedness properties
export
sortDirect : Ord a => (v : Vect n a) -> (s : Vect n a ** (v `Permutation` s, Sorted s))
sortDirect = ?sortDirect_impl
