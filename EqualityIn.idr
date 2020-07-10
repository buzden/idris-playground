module EqualityIn

interface Preorder t (po : t -> t -> Type) where
  transitive : (0 a, b, c : t) -> po a b -> po b c -> po a c
  reflexive : (0 a : t) -> po a a

interface Preorder t eq => Equivalence t (eq : t -> t -> Type) where
  symmetric : (0 a, b : t) -> eq a b -> eq b a

interface Equivalence t eq => Congruence t (f : t -> t) (eq : t -> t -> Type) where
  congruent : (0 a, b : t) -> eq a b -> eq (f a) (f b)

Preorder t Equal where
  transitive _ _ _ ab bc = trans ab bc
  reflexive _ = Refl

Equivalence t Equal where
  symmetric _ _ ab = sym ab

Congruence t f Equal where
  congruent _ _ ab = cong f ab

abba : a = b -> b = a
abba = symmetric a b
