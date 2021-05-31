module UninhProduct

import Data.Nat

Either (Uninhabited a) (Uninhabited b) => Uninhabited (a, b) where
  uninhabited (x, _) @{Left  _} = uninhabited x
  uninhabited (_, y) @{Right _} = uninhabited y

ff : Uninhabited (a, b) => Int
ff = 4

gg : Uninhabited a => Int
gg = 5

callF : Int
callF = ff {b = (Left 4 = Right 4)} {a = 5 = 4}

public export
data Lookup : a -> List (a, b) -> Type where
  Here : (y : b) -> Lookup x $ (x, y)::xys
  There : (0 _ : Uninhabited $ x === z) => Lookup z xys -> Lookup z $ (x, y)::xys

fff : (xs : List (Nat, String)) -> (n : Nat) -> (0 _ : Lookup n xs) => String

xxs : List (Nat, String)
xxs = [(1, "one"), (2, "two"), (4, "four")]

ggg1 : String
ggg1 = fff xxs 1

export
Uninhabited (a = b) => Uninhabited (S a = S b) where
  uninhabited Refl @{ab} = uninhabited @{ab} Refl

ggg2 : String
ggg2 = fff xxs 2
