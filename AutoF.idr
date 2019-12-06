module AutoF

import Data.So
import Data.Vect
import Data.Vect.Quantifiers

%default total

notEq : Eq a -> (x : a) -> (y : a) -> Type
notEq eq x y = So (x /= y)

mutual
  ||| Uqtor (uniquetor), a vector with unique values (according to `Eq`)
  data Uqt : (n : Nat) -> (a : Type) -> {auto eq : Eq a} -> Type where
    Nil  : Eq a => Uqt Z a
    (::) : (x : a) -> (xs : Uqt n a {eq}) -> {auto unq : All (notEq eq x) (unUqt xs)} -> Uqt (S n) a

  unUqt : Uqt n a {eq} -> Vect n a
  unUqt Nil     = Nil
  unUqt (x::xs) = x::(unUqt xs)

summon : {auto u : a} -> a
summon {u} = u

data X = A | B | C

Eq X where
  A == A = True
  B == B = True
  C == C = True
  _ == _ = False

-- just testing Uqt
uS : Uqt 3 String
uS = ["a", "b", "c"]

-- just testing Uqt
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

y0 : Uqt 0 X
y0 = summon

yF : Uqt 1 X
yF = summon

yG : Uqt 2 X
yG = ?yG_rhs

yHint : Uqt 3 X
yHint = ?yHint_rhs

yLoc : Uqt 3 X
yLoc =
  let a = A in
  let b = B in
  let c = C in
  ?yLoc_rhs
