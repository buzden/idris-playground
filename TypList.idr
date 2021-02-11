-- For Sergey ;-)

module TypList

import Data.List.Elem

lst1 : List Type
lst1 = [Int]

lst2 : List Type
lst2 = [forall p. Num p => p]

au : Elem x xs => Elem x xs
au @{el} = el

f : Elem Int TypList.lst2
f = au

g : Elem (forall p. Num p => p) TypList.lst1
g = au
