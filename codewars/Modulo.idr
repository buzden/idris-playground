module Modulo

import Data.Fin

%access export
%default total

add : Fin k -> Fin k -> Fin k
add {k=S k} n m = restrict k $ finToInteger n + finToInteger m

negate : Fin k -> Fin k
negate {k=S k} n = restrict k $ toIntegerNat (S k) - finToInteger n

subt : Fin k -> Fin k -> Fin k
subt {k=S k} n m = restrict k $ finToInteger n - finToInteger m + toIntegerNat (S k)

mult : Fin k -> Fin k -> Fin k
mult {k=S k} n m = restrict k $ finToInteger n * finToInteger m
