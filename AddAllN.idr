module AddAllN

-- The idea from Thorsten Altenkirch's "Why Type Theory matters" at Lambda Days 2019 --

public export
NatFun : Nat -> Type
NatFun Z = Nat
NatFun (S n) = Nat -> NatFun n

liftUnary : (Nat -> Nat) -> {n : Nat} -> NatFun n -> NatFun n
liftUnary f {n=Z}   nf = f nf
liftUnary f {n=S k} nf = liftUnary f . nf

-- You can also lift binary and `const`

export
add : {n : Nat} -> NatFun n
add {n=Z}   = 0
add {n=S k} = \n => liftUnary (n+) add

x : Nat
x = add 2 3 4 5

y : Nat
y = add 1 2
