import Data.Fin
import Data.String

Size : Type
Size = List Nat

data Coord : Size -> Type where
  Nil  : Coord []
  (::) : Fin n -> Coord ss -> Coord (n::ss)

Show (Coord s) where
  show cs = "(\{joinBy ", " $ toStrList cs})" where
    toStrList : forall s. Coord s -> List String
    toStrList [] = []
    toStrList (c::cs) = show c :: toStrList cs

foo : Coord s -> String
foo x = show x

f : String
f = foo {s=[10, 9, 8]} [5, 6, 0]
