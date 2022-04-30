import Control.Function.FunExt

import Data.Fin
import Data.List
import Data.Vect

interface HeteroFunExt where
  hFunExt : {0 b, c : a -> Type} -> {0 f : (x : a) -> b x} -> {0 g : (x : a) -> c x} -> ((x : a) -> f x ~=~ g x) -> f ~=~ g
  hFunExt' : {0 b : a -> Type} -> {0 c : a' -> Type} ->
             (0 prf : a = a') ->
             {0 f : (x : a) -> b x} -> {0 g : (x : a') -> c x} ->
             ((x' : a') -> f (rewrite prf in x') ~=~ g x') -> f ~=~ g

pr : HeteroFunExt => (f : a -> b) -> (xs : List a) -> index' (map f xs) ~=~ f . index' xs
pr f xs = hFunExt' (cong Fin $ lengthMap xs) $ pr' xs where
  pr' : (xs : List a) -> (i' : Fin $ length xs) -> index' (map f xs) (rewrite lengthMap {f} xs in i') = f (index' xs i')
  pr' (x::xs) FZ     = Refl
  pr' (x::xs) (FS y) = pr' xs y

head'map : (f : _) -> (xs : List _) -> head' (map f xs) = map f (head' xs)
head'map _ []      = Refl
head'map _ (x::xs) = Refl

ix : FunExt => (f : a -> Bool) -> Vect.findIndex f = List.head' . findIndices f
ix f = funExt r where
  r : (v : _) -> Vect.findIndex f v = head' (findIndices f v)
  r [] = Refl
  r (x::xs) with (f x)
    _ | True  = Refl
    _ | False = rewrite r xs in sym $ head'map _ _
