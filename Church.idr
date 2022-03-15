module Church

%hide Prelude.Bool

0 Bool : Type
Bool = forall a. a -> a -> a

true : Bool
true  x y = x

false : Bool
false x y = y

ifte : Bool -> a -> a -> a
ifte bool t e = bool t e

%hide Prelude.Nat

0 Nat : Type
Nat = forall a. (a -> a) -> a -> a

zero : Nat
zero f = id

one : Nat
one f = f

two : Nat
two f = f . f

incr : Nat -> Nat
incr n f = n (f . f)

add : Nat -> Nat -> Nat
add n m f = n f . m f

mul : Nat -> Nat -> Nat
mul n m f = n (m f)

decr : Nat -> Nat
decr n f x = n (\g, h => h (g f)) (const x) id

iszero : Nat -> Bool
iszero n = n (\_ => false) true

fact : Nat -> Nat
fact n = ifte (iszero n) one (n `mul` fact (decr n))

x : Nat
x = add one (mul two two)
