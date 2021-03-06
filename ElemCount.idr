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
  --IncThere : Eq a => {x, y : a} -> ElemCount c x xs -> Not (So (x == y)) -> ElemCount (weaken c) x (y :: xs)

-- TODO To define permutation through `ElemCount` (probably, the structural one)
-- TODO   and prove equivalence with the structurally defined permutation property.

(+) : Fin (S n) -> Fin (S m) -> Fin (S $ n + m)
(+) {m}     x FZ     = weakenN m x
(+) {n} {m} x (FS y) = rewrite plusSuccRightSucc n m in FS (x + y)

ecConcPresSum : ElemCount ca x as -> ElemCount cb x bs -> ElemCount (ca + cb) x (as ++ bs)
ecConcPresSum = ?ecConcPresSum_impl

||| Proof that permutationproperty preserves elements (i.e. preserves elements count)
permPresElems : Permutation xs ys -> ElemCount n e xs -> ElemCount n e ys
permPresElems EmptyPerm ec = ec
permPresElems {xs=a::as} (InsertPerm ip) (IncHere iec) = ?perm_here
permPresElems (InsertPerm ip) (IncThere iec xy) = ?perm_there
