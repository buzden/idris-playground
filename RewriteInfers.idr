module RewriteInfers

import Data.Vect

namespace SimpleWordy

  f : m = n -> Vect n Nat -> Vect (S m) Nat
  f eq xs = let ys = rewrite eq in xs
            in 0 :: ys

namespace SimpleTacit

  f : m = n -> Vect n Nat -> Vect (S m) Nat
  f Refl xs = 0 :: xs

namespace NoRefl

  g : {0 xs, ys : List b} -> length xs = length ys -> Vect (length ys) Nat -> Vect (S $ length xs) Nat
  g eq xs = let ys = rewrite eq in xs
            in 0 :: ys
