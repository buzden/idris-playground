module Sortings

import Data.Fin
import Data.Vect

%default total

count : Eq a => a -> Vect n a -> Fin (S n)
count _ Nil = 0
count x (y :: xs) = (if x == y then FS else weaken) $ count x xs

data ElemCount : Fin (S n) -> a -> Vect n a -> Type where
  NoElem   :                                                             ElemCount FZ         x []
  IncHere  : ElemCount c x xs                                         -> ElemCount (FS c)     x (x :: xs)
  IncThere : Eq a => {x, y : a} -> ElemCount c x xs -> x == y = False -> ElemCount (weaken c) x (y :: xs)

  -- Variant with structural equality instead of `Eq`:
  --IncThere : ElemCount c x xs -> Not (x = y) -> ElemCount (weaken c) x (y :: xs)

Permutation : Vect n a -> Vect n a -> Type
Permutation xs ys = ?perm

(<=) : Ord a => a -> a -> Type
x <= y = (x <= y) = True

data Sorted : Vect n a -> Type where
  Empty     :                                                    Sorted []
  Singleton :                                                    Sorted [x]
  Comp      : Ord a => {x, y : a} -> Sorted (x::xs) -> y <= x -> Sorted (y::x::xs)

||| Sorting with direct encoding of first-order logic formulae of sortedness properties
sortDirect : (v : Vect n a) -> (s : Vect n a ** (v `Permutation` s, Sorted s))
sortDirect = ?sortDirect

--||| An attempt to formulate properties of sortedness using structural things (like `Fin n`)
--sortStructural : Type
--sortStructural = ?sortStructural
