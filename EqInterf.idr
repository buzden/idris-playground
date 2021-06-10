module EqInterf

infix 6 =~=

interface Equ ty where
  data (=~=) : ty -> ty -> Type

  0 fromPropositional : {0 x, y : ty} -> (0 _ : x = y) -> x =~= y

  0 reflexivity  : {0 x : ty} -> x =~= x
  0 symmetry     : {0 x, y : ty} -> (0 _ : x =~= y) -> y =~= x
  0 transitivity : {0 x, y, z : ty} -> (0 _ : x =~= y) -> (0 _ : y =~= z) -> x =~= z

interface Equ ty => EquProp ty where
  0 equIsProp : (=~=) {ty} = Equal

interface Equ ty => Cong ty where -- couldn't made it a part of the `Equ` interface...
  0 congruence : Equ tu => (0 f : ty -> tu) -> {0 x, y : ty} -> (0 _ : x =~= y) -> f x =~= f y

--interface Equ a => Equ b => Inj (0 f : a -> b) where
--  0 injectivity : {0 x, y : a} -> (0 _ : f x =~= f y) -> x =~= y

Equ Nat where
  (=~=) = Equal

  fromPropositional Refl = Refl

  reflexivity  = Refl
  symmetry     = sym
  transitivity = trans

EquProp Nat where
  equIsProp = Refl

Cong Nat where
  congruence _ Refl = reflexivity

[WeakFunext] Equ b => Equ (a -> b) where
  f =~= g = (x : a) -> f x =~= g x

  fromPropositional Refl = \_ => reflexivity

  reflexivity      = \_ => reflexivity
  symmetry p       = \x => symmetry $ p x
  transitivity p q = \x => transitivity (p x) (q x)

[WeakFunextCong] Equ b => Cong (a -> b) using WeakFunext where
  congruence {x=f} {y=g} h xy = ?foo

[StrongFunext] Cong a => Equ b => Equ (a -> b) where
  f =~= g = (x, y : a) -> x =~= y -> f x =~= g y

  fromPropositional {y=f} Refl = \_, _, xy => congruence f xy

  reflexivity {x=f} = \_, _, xx => congruence f xx
  symmetry {x=f} {y=g} fg = \x, y, xy => symmetry $ fg y x $ symmetry xy
  transitivity {x=f} {y=g} {z=h} fg gh = \x, y, xy => fg x y xy `transitivity` gh y y reflexivity

[StrongFunextCong] Cong a => Equ b => Cong (a -> b) using StrongFunext where
  congruence {x=f} {y=g} h xy = ?foo0 -- \u, v, uv => ?foo
