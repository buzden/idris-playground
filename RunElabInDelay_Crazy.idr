import Language.Reflection

%language ElabReflection

%default total

data X : Type -> Type where

f : List (Unit, Inf (X a)) -> X a

scr : Elab $ X a
scr = fail "before all"

nats : X Nat
nats = f [ ?foo, ((), %runElab scr) ]

-- {-

nn : Nat -> Nat

ns : Nat -> Stream Nat
ns x = x :: ns (S x)

s : Stream Nat
s = ns Z
