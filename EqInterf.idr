module EqInterf

import Data.Nat

infix 6 =~=

--------------------------------------------------
--- Interfaces and general functions over them ---
--------------------------------------------------

interface Equ ty where
  data (=~=) : ty -> ty -> Type

  0 fromPropositional : {0 x, y : ty} -> (0 _ : x = y) -> x =~= y

  0 reflexivity  : {0 x : ty} -> x =~= x
  0 symmetry     : {0 x, y : ty} -> (0 _ : x =~= y) -> y =~= x
  0 transitivity : {0 x, y, z : ty} -> (0 _ : x =~= y) -> (0 _ : y =~= z) -> x =~= z

interface Equ ty => Transp ty where
  0 transport : (0 p : ty -> Type) -> {0 x, y : ty} -> (0 _ : x =~= y) -> p x -> p y

0 congruence : Transp ty => Equ tu => (0 f : ty -> tu) -> {0 x, y : ty} -> (0 _ : x =~= y) -> f x =~= f y
congruence f xy = transport (\i => f x =~= f i) xy reflexivity

interface Equ ty => EquProp ty where
  0 equIsProp : (=~=) {ty} = Equal

--interface Equ t => Equ u => Cong t u (0 f : t -> u) where
--  0 congruence : {0 x, y : t} -> (0 _ : x =~= y) -> f x =~= f y

interface Equ t => Equ u => Inj t u (0 f : t -> u) where
  0 injectivity : {0 x, y : t} -> (0 _ : f x =~= f y) -> x =~= y

---------------------------------------------
--- Interfaces' implementations for `Nat` ---
---------------------------------------------

Equ Nat where
  (=~=) = Equal

  fromPropositional Refl = Refl

  reflexivity  = Refl
  symmetry     = sym
  transitivity = trans

Transp Nat where
  transport _ Refl p = p

EquProp Nat where
  equIsProp = Refl

Inj _ _ S where
  injectivity Refl = Refl

0 injPlusL : {n : Nat} -> (n + x = n + y) -> x = y
injPlusL {n=Z}   eq = eq
injPlusL {n=S k} eq = injPlusL $ injectivity {f=S} eq

Inj Nat _ (n+) where
  injectivity eq = injPlusL eq

Inj Nat _ (+n) where
  injectivity eq = injPlusL {n} rewrite plusCommutative n x in rewrite plusCommutative n y in eq

----------------------------------------------------------
--- Equality for functions as functional extensinality ---
----------------------------------------------------------

[WeakFunext] Equ b => Equ (a -> b) where
  f =~= g = (x : a) -> f x =~= g x

  fromPropositional Refl = \_ => reflexivity

  reflexivity      _ = reflexivity
  symmetry p       x = symmetry $ p x
  transitivity p q x = transitivity (p x) (q x)

[WeakFunextTransp] Equ b => Transp (a -> b) using WeakFunext where
  transport {x=f} {y=g} pr fg p = ?foo_transport

[StrongFunext] Transp a => Equ b => Equ (a -> b) where
  f =~= g = (x, y : a) -> x =~= y -> f x =~= g y

  fromPropositional {y=f} Refl = \_, _, xy => congruence f xy

  reflexivity {x=f} = \_, _, xx => congruence f xx
  symmetry {x=f} {y=g} fg = \x, y, xy => symmetry $ fg y x $ symmetry xy
  transitivity {x=f} {y=g} {z=h} fg gh = \x, y, xy => fg x y xy `transitivity` gh y y reflexivity

[StrongFunextTransp] Transp a => Equ b => Transp (a -> b) using StrongFunext where
  transport {x=f} {y=g} pr fg p = ?foo0
