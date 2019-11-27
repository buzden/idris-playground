module ElemCount

import Data.Vect
import Sortings

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

||| Permutation property defined through `ElemCount`
data PermTEC : Vect n a -> Vect n a -> Type where
  Perm : {xs, ys : Vect n a} -> ({c : Fin (S n)} -> {x : a} -> ElemCount c x xs -> ElemCount c x ys) -> PermTEC xs ys
