module VectorsAndLists

import Data.List
import Data.Vect

%default total

list2vec : (l : List a) -> Vect (length l) a
list2vec [] = []
list2vec (x::xs) = x :: list2vec xs

safeToVec : List a -> Maybe (Vect n a)
safeToVec {n} l = if length l == n
                    then Just $ list2vec l -- need a proof that length l = n
                    else Nothing
