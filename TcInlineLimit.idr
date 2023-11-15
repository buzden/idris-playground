%default total

%tcinline
addNTimes : Semigroup a => Nat -> (seed : a) -> a -> a
addNTimes Z     i x = x
addNTimes (S n) i x = i <+> addNTimes n i x

data X a = Empty | NonEmpty a (X a)

Semigroup a => Semigroup (X a) where
  Empty <+> xs = xs
  xs <+> Empty = xs
  NonEmpty x xs <+> NonEmpty y ys = NonEmpty (x <+> y) (addNTimes 100 xs ys)
