module VectorsAndLists

import Data.List
import Data.Vect

%default total

list2vec : (l : List a) -> Vect (length l) a
list2vec [] = []
list2vec (x::xs) = x :: list2vec xs
