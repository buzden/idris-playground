module AutoF

import Data.Vect
import Data.Vect.Quantifiers

%default total

||| Uqtor (uniquetor) data type ;-)
data Uqt : (n : Nat) -> (a : Type) -> Vect n a -> Type where
  Nil  : Uqt Z a []
  (::) : (x : a) -> Uqt n a xs -> {auto ev : All (\y => Not (x = y)) xs} -> Uqt (S n) a (x :: xs)

unUqt : Uqt n a xs -> Vect n a
unUqt {xs} _ = xs

x : {auto uqt : Uqt 3 String xs} -> Vect 3 String
x {uqt} = unUqt uqt

-- %hint
a : String
a = "asdf"

u : Uqt 3 String xs
u = ["a", "b", "c"]

y : Vect 3 String
y =
  let a = "asdf" in
  let b = "asdg" in
  let c = "asdh" in
  ?x
