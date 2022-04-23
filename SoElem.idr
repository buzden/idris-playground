import Data.So
import Data.List.Quantifiers

%default total

soElemToAny : Eq a => (x : a) -> (list : List a) -> So (elem x list) -> Any (\y => So $ x == y) list
soElemToAny x [] so with (elem x []) proof prf
  _ | True = absurd prf
soElemToAny x (l::ls) so with (x == l) proof prf
  _ | True  = Here $ rewrite prf in Oh
  _ | False = There $ soElemToAny x ls so

foldlOrTrue : (ls : List a) -> (f : _) -> So (foldl (\acc, elem => acc || f elem) True ls)
foldlOrTrue []      _ = Oh
foldlOrTrue (_::xs) f = foldlOrTrue xs f

anyToSoElem : Eq a => (x : a) -> (list : List a) -> Any (\y => So $ x == y) list -> So $ elem x list
anyToSoElem x (l::ls) (Here y) with (x == l)
  _ | True = foldlOrTrue ls _
anyToSoElem x (l::ls) (There y) with (x == l)
  _ | True  = foldlOrTrue ls _
  _ | False = anyToSoElem x ls y
