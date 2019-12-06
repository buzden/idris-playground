module AutoF

import Data.So
import Data.Vect
import Data.Vect.Quantifiers

%default total

notEq : Eq a -> (x : a) -> (y : a) -> Type
notEq eq x y = So (x /= y)

mutual
  ||| Uqtor (uniquetor): a vector with unique values (according to `Eq`)
  data Uqt : (n : Nat) -> (a : Type) -> {auto eq : Eq a} -> Type where
    Nil  : Eq a => Uqt Z a
    (::) : (x : a) -> (xs : Uqt n a {eq}) -> {auto ev : All (notEq eq x) (unUqt xs)} -> Uqt (S n) a

  unUqt : Uqt n a {eq} -> Vect n a
  unUqt Nil = Nil
  unUqt (x::xs) = x::(unUqt xs)

x : {auto uqt : Uqt 3 a {eq}} -> Vect 3 a
x {uqt} = unUqt uqt

data X = A | B | C

Eq X where
  A == A = True
  B == B = True
  C == C = True
  _ == _ = False

uS : Uqt 3 String
uS = ["a", "b", "c"]

uX : Uqt 3 X
uX = [A, B, C]

%hint
a : X
a = A

%hint
b : X
b = B

%hint
c : X
c = C

yHint : Vect 3 X
yHint = ?x

yLoc : Vect 3 X
yLoc =
  let a = A in
  let b = B in
  let c = C in
  ?x
