import Control.Relation

import Data.So

%default total

dropAll : Eq a => a -> List a -> List a
dropAll _ []      = []
dropAll y (x::xs) = if y == x then dropAll y xs else x :: dropAll y xs

dropAll_decrements_or_stalls : Eq a =>
                               Reflexive a (So .: (==)) =>
                               (x : a) ->
                               (xs : List a) ->
                               dropAll x (x::xs) = dropAll x xs
dropAll_decrements_or_stalls @{_} @{refl} x xs with (reflexive @{refl} {x}) | (x==x)
  _ | _ | True = Refl
