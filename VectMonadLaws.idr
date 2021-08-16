module VectMonadLaws

import Data.Vect

%default total

mapFuses : (g : b -> c) -> (f : a -> b) -> (xs : Vect n a) -> map g (map f xs) = map (g . f) xs
mapFuses g f []      = Refl
mapFuses g f (_::xs) = rewrite mapFuses g f xs in Refl

bindPureIsMap : (xs : Vect n a) -> (f : a -> b) -> map f xs = xs >>= \x => pure $ f x
bindPureIsMap [] f = Refl
bindPureIsMap {n=S n} (_::xs) f = rewrite bindPureIsMap xs f in
                                  rewrite mapFuses tail (\x => f x :: replicate n (f x)) xs in
                                  Refl

apThruBind' : (fs : Vect n (a -> b)) -> (xs : Vect n a) -> fs <*> xs = fs >>= (`map` xs)
apThruBind' [] [] = Refl
apThruBind' (_::fs) (x::xs) = rewrite mapFuses tail (\f' => f' x :: map f' xs) fs in
                              rewrite apThruBind' fs xs in
                              Refl

0 funext : {f, g : a -> b} -> ((x : a) -> f x = g x) -> f = g
funext _ = believe_me $ the (0 = 0) Refl

apThruBind : (fs : Vect n (a -> b)) -> (xs : Vect n a) -> fs <*> xs = fs >>= \f' => xs >>= \x' => pure (f' x')
apThruBind fs xs = trans (apThruBind' fs xs) $
                     cong diag $ cong (`map` fs) $
                       funext $ bindPureIsMap xs
