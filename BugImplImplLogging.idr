import Data.Vect

%logging "elab" 100

[Named] {n : Nat} -> Show (Vect n a) where
  show x = "whatever"
