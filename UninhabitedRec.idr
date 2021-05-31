module UninhabitedRec

import Data.Nat
import Data.List.Elem

--Either (Uninhabited a) (Uninhabited b) => Uninhabited (a, b) where
--  uninhabited (x, _) @{Left  _} = uninhabited x
--  uninhabited (_, y) @{Right _} = uninhabited y

ff : Uninhabited (a, b) => Int
ff = 4

callF : Int
callF = ff {b = (Left 4 = Right 4)} {a = 5 = 4}

------------------

data Lookup : a -> List (a, b) -> Type where
  Here : (y : b) -> Lookup x $ (x, y)::xys
  There : (0 _ : Uninhabited $ x === z) => Lookup z xys -> Lookup z $ (x, y)::xys

fff : (xs : List (Nat, String)) -> (n : Nat) -> (0 _ : Lookup n xs) => String

xxs : List (Nat, String)
xxs = [(1, "one"), (2, "two"), (4, "four")]

lkup1 : String
lkup1 = fff xxs 1

--export
--Uninhabited (a = b) => Uninhabited (S a = S b) where
--  uninhabited Refl @{ab} = uninhabited @{ab} Refl

lkup2 : String
lkup2 = fff xxs 2

lkup3 : String
lkup3 = fff xxs 3

------------------

data Uniq : Type -> Type

toList : Uniq a -> List a

data Uniq : Type -> Type where
  Nil  : Uniq a
  (::) : (x : a) -> (xs : Uniq a) -> Uninhabited (Elem x $ toList xs) => Uniq a

toList [] = []
toList (x::xs) = x :: toList xs

uniqGood : Uniq Nat
uniqGood = [1, 2, 3]

uniqBad : Uniq Nat
uniqBad = [1, 2, 1]
