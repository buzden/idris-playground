import Data.Nat

%default total

-- `k` divides by `n`
data DivsBy : (k, n : Nat) -> Type where
  DS : (m : Nat) -> (k = m * S n) -> k `DivsBy` S n

d4e' : n `DivsBy` 4 -> n `DivsBy` 2
d4e' (DS 0 Refl) = DS 0 Refl
d4e' (DS 1 Refl) = DS 2 Refl
d4e' (DS m Refl) = DS (2 * m) $ do
  rewrite multAssociative m 2 2
  rewrite multCommutative m 2
  rewrite plusZeroRightNeutral m
  Refl

divTrans : a `DivsBy` b -> b `DivsBy` c -> a `DivsBy` c
divTrans {b=S b} {c=S c} (DS ab np) (DS bc mp) = DS _ $ do
  rewrite np
  rewrite mp
  rewrite multAssociative ab bc (S c)
  Refl

spl : {a, b : _} -> k `DivsBy` (a * b) -> k `DivsBy` a
spl {a=S a} {b=Z} d = case the (DivsBy k 0) $ rewrite sym $ multCommutative a 0 in d of _ impossible
spl {a=S a} {b=S b} (DS kab Refl) = DS _ $ do
  rewrite multCommutative (S a) (S b)
  rewrite multAssociative kab (S b) (S a)
  Refl
