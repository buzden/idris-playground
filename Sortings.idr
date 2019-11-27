module Sortings

import Data.Fin
import Data.Vect
import Data.So

%default total

count : Eq a => a -> Vect n a -> Fin (S n)
count _ Nil = 0
count x (y :: xs) = (if x == y then FS else weaken) $ count x xs

data ElemCount : Fin (S n) -> a -> Vect n a -> Type where
  NoElem   :                                    ElemCount FZ         x []
  IncHere  : ElemCount c x xs                -> ElemCount (FS c)     x (x :: xs)
  IncThere : ElemCount c x xs -> Not (x = y) -> ElemCount (weaken c) x (y :: xs)

  -- A variant with non-structural equality
  --IncThere : Eq a => {x, y : a} -> ElemCount c x xs -> x == y = False -> ElemCount (weaken c) x (y :: xs)

-- TODO To define permutation through `ElemCount` (probably, the structural one)
-- TODO   and prove equivalence with the structurally defined permutation property.

||| Structural inductive rules for prooving that one vector is a permutation of another.
data Permutation : Vect n a -> Vect n a -> Type where
  EmptyPerm  : Permutation [] []
  InsertPerm : {lys : Vect lm a} -> {rys : Vect rm a}
            -> Permutation xs (lys ++ rys) -> Permutation (x::xs) (rewrite plusSuccRightSucc lm rm in lys ++ x::rys)

data Sorted : Vect n a -> Type where
  Empty     :                                                         Sorted []
  Singleton :                                                         Sorted [x]
  Comp      : Ord a => {x, y : a} -> Sorted (x::xs) -> So (y <= x) -> Sorted (y::x::xs)

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
sortDirect : (v : Vect n a) -> (s : Vect n a ** (v `Permutation` s, Sorted s))
sortDirect = ?sortDirect_impl
