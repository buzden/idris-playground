import Data.Vect

-- `minus` is saturating subtraction, so this works like we want it to
eq_max : (n, k : Nat) -> maximum k n = plus (n `minus` k) k
eq_max  n     Z    = rewrite minusZeroRight n in rewrite plusZeroRightNeutral n in Refl
eq_max  Z    (S _) = Refl
eq_max (S n) (S k) = rewrite sym $ plusSuccRightSucc (n `minus` k) k in rewrite eq_max n k in Refl

leftPad : (x : a) -> (n : Nat) -> (xs : Vect k a) -> Vect (maximum k n) a
leftPad {k} x n xs = rewrite eq_max n k in replicate (n `minus` k) x ++ xs

leftPadProp : {xs : Vect k a} -> (m : Nat ** leftPad x n xs = {- rewrite somehow? `the Type (rewrite xxx in replicate ...)`? -} replicate m x ++ xs)
leftPadProp {n} {k} = (n `minus` k ** ?x)
