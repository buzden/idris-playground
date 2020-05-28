x : {default Integer 0 a : Type} -> (Num a, Neg a) => a
x = -1

y : Double
y = 1 + x

description : String
description = show x
