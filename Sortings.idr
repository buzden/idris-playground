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
  --IncThere : ElemCount c x xs -> x = y -> Void -> ElemCount (weaken c) x (y :: xs)

Permutation : Vect n a -> Vect n a -> Type
Permutation xs ys = ?perm

LTE : Ord a => a -> a -> Type
LTE x y = (x <= y) = True
-- #. Can we name `LTE` as `(<=)`?
-- #. Why if we do so, `sortDirect` stops to typecheck?

data Sorted : Vect n a -> Type where
  Empty     :                                       Sorted []
  Singleton :                                       Sorted [a]
  Comp      : Ord a => Sorted (x::xs) -> LTE y x -> Sorted (y::x::xs)

||| Sorting with direct encoding of first-order logic formulae of sortedness properties
sortDirect : (v : Vect n a) -> (s : Vect n a ** (v `Permutation` s, Sorted s))
sortDirect = ?sortDirect

--||| An attempt to formulate properties of sortedness using structural things (like `Fin n`)
--sortStructural : Type
--sortStructural = ?sortStructural
