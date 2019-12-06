module AutoF

import Data.So
import Data.Vect
import Data.Vect.Quantifiers

%default total

notEq : Eq a -> (x : a) -> (y : a) -> Type
notEq eq x y = So (x /= y)

||| Uqtor (uniquetor): a wrapper of vector with unique values ;-)
data Uqt : (n : Nat) -> (a : Type) -> {auto eq : Eq a} -> Vect n a -> Type where
  Nil  : Eq a => Uqt Z a []
  (::) : (x : a) -> Uqt n a {eq} xs -> {auto ev : All (notEq eq x) xs} -> Uqt (S n) a (x :: xs)

unUqt : Eq a => Uqt n a xs -> Vect n a
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
