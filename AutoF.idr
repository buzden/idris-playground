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

x : Eq a => {auto uqt : Uqt 3 a xs} -> Vect 3 a
x {uqt} = unUqt uqt

data X = A | B | C

Eq X where
  A == A = True
  B == B = True
  C == C = True
  _ == _ = False

%hint
a : X
a = A

%hint
b : X
b = B

%hint
c : X
c = C

uS : (xs ** Uqt 3 String xs)
uS = (_ ** ["a", "b", "c"])

uX : (xs ** Uqt 3 X xs)
uX = (_ ** [A, B, C])

yHint : Vect 3 X
yHint = x

yLoc : Vect 3 X
yLoc =
  let a = A in
  let b = B in
  let c = C in
  ?x
