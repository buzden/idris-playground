module TwoRepeats

import Data.Stream

%default total

public export
repeat : a -> Stream a
repeat x = xs where
  xs : Stream a
  xs = x :: xs

public export
repeat' : a -> Stream a
repeat' x = x :: repeat' x

repeatsTheSame : (x : a) -> TwoRepeats.repeat x = repeat' x
repeatsTheSame x = ?repeatsTheSame_rhs -- Refl here hangs the typechecker.
