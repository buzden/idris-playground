module TakeLemma

import Control.Function

import Data.List

takeNilNil : (i : Nat) -> List.take i [] === []
takeNilNil Z     = Refl
takeNilNil (S k) = Refl

sMin : (i, j : Nat) -> S i `min` S j = S (i `min` j)
sMin i j with (compareNat i j)
  _ | LT = Refl
  _ | GT = Refl
  _ | EQ = Refl

takeTakeMin : (i, j : Nat) -> (xs : List a) -> take i (take j xs) === take (i `min` j) xs
takeTakeMin Z     Z     xs = Refl
takeTakeMin Z     (S _) xs = Refl
takeTakeMin (S i) Z     xs = Refl
takeTakeMin (S i) (S j) []      = sym $ takeNilNil _
takeTakeMin (S i) (S j) (x::xs) = do
  rewrite sMin i j
  rewrite takeTakeMin i j xs
  Refl

takeLemma_bwd : (xs, ys : List a) -> xs = ys -> (i : Nat) -> take i xs === take i ys
takeLemma_bwd xs xs Refl i = Refl

takeLemma_fwd : (xs, ys : List a) -> (forall i. take i xs === take i ys) -> xs = ys
takeLemma_fwd []      []      f = Refl
takeLemma_fwd []      (y::ys) f = absurd $ f {i=1}
takeLemma_fwd (x::xs) []      f = absurd $ f {i=1}
takeLemma_fwd (x::xs) (y::ys) f = do
  let Refl = f {i=1}
  let l : forall i. take i xs = take i ys
      l = snd $ biinj (::) $ f {i=S i}
  cong (x::) $ takeLemma_fwd xs ys l
