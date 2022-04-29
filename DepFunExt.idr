import Control.Function.FunExt

import Data.Fin
import Data.List

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
