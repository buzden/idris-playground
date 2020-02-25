module RevRev

namespace Preloaded
  %access public export
  %default total

  rev : List x -> List x
  rev [] = []
  rev (y :: xs) = rev xs ++ [y]

%access export
%default total

revrevid : (a : List x) -> (rev (rev a)) = a
revrevid = ?oh_my_god_how_do_I_prove_this
