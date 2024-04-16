import Data.List
import Data.List.Elem
import Data.List.Quantifiers

add4 : Nat -> Nat
add4 x = S $ S $ S $ S x

data IsAdded4 : Nat -> Nat -> Type where
  ItIsAdded4 : IsAdded4 x (S $ S $ S $ S x)

x : IsAdded4 5 9
x = ItIsAdded4

x' : IsAdded4 0 4
x' = ItIsAdded4

x'' : IsAdded4 15 19
x'' = ItIsAdded4

data HasAdded : a -> (xs, ys : List a) -> Type where
  AddedIndeed : (x : a) -> Elem x ys -> All (\x => Elem x ys) xs -> HasAdded x xs ys

h : HasAdded 5 [1, 2, 3] [3, 2, 5, 1]
h = %search

h' : HasAdded 5 [1, 2, 3] [3, 2, 5, 6, 1]
h' = %search

data HasAddedStrict : a -> (xs, ys : List a) -> Type where
  AddedIndeedStrict : All (\e => Elem e ys) (x::xs) -> All (\e => Elem e $ x::xs) ys -> HasAddedStrict x xs ys

hs : HasAddedStrict 5 [1, 2, 3] [3, 2, 5, 1]
hs = %search

failing
  hs' : HasAddedStrict 5 [1, 2, 3] [3, 2, 5, 6, 1]
  hs' = %search
