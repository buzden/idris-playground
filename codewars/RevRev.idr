module RevRev

namespace Preloaded
  %access public export
  %default total

  rev : List x -> List x
  rev [] = []
  rev (y :: xs) = rev xs ++ [y]

%access export
%default total

lemma : (xs : List x) -> (y : x) -> rev (xs ++ [y]) = y :: rev xs
lemma []      _ = Refl
lemma (_::as) y = rewrite lemma as y in Refl

revrevid : (a : List x) -> (rev (rev a)) = a
revrevid []      = Refl
revrevid (a::as) = rewrite lemma (rev as) a in
                   rewrite revrevid as in
                   Refl
