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

export
total doubleNotDisappears : (b : Bool) -> not (not b) = b
doubleNotDisappears True  = Refl
doubleNotDisappears False = Refl

export
takeSoConjPart : So b -> So (b && c) -> So c
takeSoConjPart sb sbc with (sb)
  takeSoConjPart _ sbc | Oh with (sbc)
    takeSoConjPart _ _ | Oh | Oh = Oh

export
soConjAbsurd : So b -> So (not b && c) -> Void
soConjAbsurd sb sbc with (sb)
  | Oh = uninhabited sbc

export
splitSoConj : So (b && c) -> (So b, So c)
splitSoConj {b} sbc = case choose b of
  Left sb => (sb, takeSoConjPart sb sbc)
  Right snb => absurd $ soConjAbsurd snb (rewrite doubleNotDisappears b in sbc)

namespace SortedProperties
  export
  valueToType : Ord a => So (Sortings.sorted xs) -> Sorted xs
  valueToType {xs=[]}       _  = Empty
  valueToType {xs=[_]}      _  = Singleton
  valueToType {xs=y::x::xs} so = let (soyx, soxxs) = splitSoConj so in
                                 Comp (valueToType soxxs) soyx

  export
  notValueToNotType : Ord a => So (not $ Sortings.sorted xs) -> Not (Sorted xs)
  notValueToNotType = ?notValueToNotType_impl

  export
  typeToValue : Ord a => Sorted xs -> So (Sortings.sorted xs)
  typeToValue = ?typeToValue_impl

  export
  notTypeToNotValue : Ord a => Not (Sorted xs) -> So (not $ Sortings.sorted xs)
  notTypeToNotValue = ?notTypeToNotValue_impl

||| Sorting with direct encoding of first-order logic formulae of sortedness properties
export
sortDirect : Ord a => (v : Vect n a) -> (s : Vect n a ** (v `Permutation` s, Sorted s))
sortDirect = ?sortDirect_impl
