module AppendInjective

%access export
%default total

appendInjectiveRight : (a, b, c : List x) -> a ++ b = a ++ c -> b = c
appendInjectiveRight []      _ _ = id
appendInjectiveRight (y::ys) b c = appendInjectiveRight ys b c . snd . consInjective

lemma_bad_nat : (a, b : Nat) -> S a + b = b -> Void
lemma_bad_nat a Z     = rewrite plusZeroRightNeutral a in SIsNotZ
lemma_bad_nat a (S k) = rewrite sym $ plusSuccRightSucc a k in
                        lemma_bad_nat a k . succInjective (S (a + k)) k

lemma_bad_append : (x : a) -> (xs, ys : List a) -> (x::xs) ++ ys = ys -> Void
lemma_bad_append x xs ys = lemma_bad_nat (length xs) (length ys) . rewrite sym $ lengthAppend xs ys in cong {f=length}

appendInjectiveLeft : (a, b, c : List x) -> a ++ c = b ++ c -> a = b
appendInjectiveLeft [] [] _ _ = Refl
appendInjectiveLeft (y::ys) (z::zs) c prf with (consInjective prf)
  | (p1, p2) = rewrite p1 in cong $ appendInjectiveLeft ys zs c p2
appendInjectiveLeft [] (z::zs) c prf = absurd $ lemma_bad_append z zs c $ sym prf
appendInjectiveLeft (y::ys) [] c prf = absurd $ lemma_bad_append y ys c prf
