module ABMinus

mm : (a, b : Nat) -> a `minus` b = (S a `minus` b) `minus` 1
mm Z     Z     = Refl
mm Z     (S _) = Refl
mm (S a) Z     = Refl
mm (S a) (S b) = rewrite mm a b in Refl

ms : (a, b : Nat) -> a `minus` S b = (a `minus` b) `minus` 1
ms Z     b     = Refl
ms (S _) Z     = Refl
ms (S a) (S b) = rewrite ms a b in Refl

abm : (a, b : Nat) -> a `minus` (b + 1) = (a `minus` b) `minus` 1
abm Z     Z     = Refl
abm (S k) Z     = Refl
abm Z     (S _) = Refl
abm (S a) (S b) = rewrite abm a b in Refl
