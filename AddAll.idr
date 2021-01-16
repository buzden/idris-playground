module AddAll

-- The idea from Thorsten Altenkirch's "Why Type Theory matters" at Lambda Days 2019 --

public export
data NatFun : a -> Type where
  SZ : NatFun Nat
  SS : NatFun x -> NatFun (Nat -> x)

liftUnary : (Nat -> Nat) -> NatFun a => a -> a
liftUnary f @{SZ}   nf = f nf
liftUnary f @{SS s} nf = liftUnary f . nf

-- You can also lift binary and `const`

export
add : NatFun a => a
add @{SZ}   = 0
add @{SS s} = \n => liftUnary (n+) add

x : Nat
x = add 2 3 4 5

y : Nat
y = add 1 2
