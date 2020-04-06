module Polunin

import Data.So

%default total

foo : (x : Int) -> {auto xBound : So (x >= 0 && x <= 10)} -> (y : Int ** y = x * 2)
foo x = (x * 2 ** Refl)

a : Int
a = 5

bf : Int
bf = fst $ foo a

b : (x : Int ** x = 10)
b = foo a
