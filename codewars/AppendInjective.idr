module AppendInjective

%access export
%default total

appendInjectiveRight : (a, b, c : List x) -> a ++ b = a ++ c -> b = c
appendInjectiveRight []      _ _ = id
appendInjectiveRight (y::ys) b c = appendInjectiveRight ys b c . snd . consInjective

lemma_bad_append : (x : a) -> (xs, ys : List a) -> (x::xs) ++ ys = ys -> whatever
lemma_bad_append x xs []      = absurd . lemma_val_not_nil
lemma_bad_append x xs (y::ys) = lemma_bad_append x xs ys . ?lemma_bad_append_rhs_3

appendInjectiveLeft : (a, b, c : List x) -> a ++ c = b ++ c -> a = b
appendInjectiveLeft [] [] _ _ = Refl
appendInjectiveLeft (y::ys) (z::zs) c prf with (consInjective prf)
  | (p1, p2) = rewrite p1 in cong $ appendInjectiveLeft ys zs c p2
appendInjectiveLeft [] (z::zs) c prf = lemma_bad_append z zs c $ sym prf
appendInjectiveLeft (y::ys) [] c prf = lemma_bad_append y ys c prf
