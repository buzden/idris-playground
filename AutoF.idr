module AutoF

import Data.So
import Data.Vect

%default total

notEq : Eq a -> (x : a) -> (y : a) -> Type
notEq eq x y = So (x /= y)

namespace Quantifiers
  ||| A proof that all elements of a vector satisfy a property. It is a list of
  ||| proofs, corresponding element-wise to the `Vect`.
  -- Copied from Idris 1's base's Data.Vect.Quantifiers
  public export
  data All : (P : a -> Type) -> Vect n a -> Type where
    Nil : {P : a -> Type} -> All P Nil
    (::) : {P : a -> Type} -> {xs : Vect n a} -> P x -> All P xs -> All P (x :: xs)

mutual
  ||| Uqtor (uniquetor): a vector with unique values (according to `Eq`)
  data Uqt : (n : Nat) -> (a : Type) -> {auto eq : Eq a} -> Type where
    Nil  : Eq a => Uqt Z a
    (::) : (x : a) -> (xs : Uqt n a {eq}) -> {auto ev : All (notEq eq x) (unUqt xs)} -> Uqt (S n) a

  unUqt : Uqt n a {eq} -> Vect n a
  unUqt Nil     = Nil
  unUqt (x::xs) = x::(unUqt xs)

x : {auto uqt : Uqt n a {eq}} -> Vect n a
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

y0 : Vect 0 X
y0 = x

yF : Vect 1 X
yF = x

yG : Vect 2 X
yG = ?yG_rhs

yHint : Vect 3 X
yHint = ?yHint_rhs

yLoc : Vect 3 X
yLoc =
  let a = A in
  let b = B in
  let c = C in
  ?yLoc_rhs
