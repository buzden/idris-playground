-- Code based on the question in the Idris mailing list

import Data.Vect

public export
group : (n : Nat) -> (m : Nat) -> Vect (n * m) a -> Vect n (Vect m a)
group Z     _ _  = []
group (S n) m xs = let (l, r) = splitAt m xs in l :: group n m r

public export
group' : (n : Nat) -> (m : Nat) -> Vect (n * m) a -> Vect m (Vect n a)
group' n m xs = group m n $ rewrite multCommutative m n in xs

export
splitAtConcatRev : (n : Nat) -> (xs : Vect (n + m) a) -> {0 l : Vect n a} -> {0 r : Vect m a} -> splitAt n xs = (l, r) -> l ++ r = xs
splitAtConcatRev Z _ Refl = Refl
splitAtConcatRev (S n) (x::xs) {l} prf with (splitAt n xs) proof sprf
  splitAtConcatRev (S n) (x::xs) {l=x::l} Refl | (l, r) = cong (x::) $ splitAtConcatRev n xs sprf

public export
concat_group_id : (n : Nat) -> (m : Nat) -> (v : Vect (n * m) a) -> concat (group n m v) = v
concat_group_id Z     _ [] = Refl
concat_group_id (S n) m xs with (splitAt m xs) proof prf
  _ | (l, r) = rewrite concat_group_id n m r in splitAtConcatRev m xs prf
