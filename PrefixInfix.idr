module PrefixInfix

infixr 1 <><>

prefix 1 .>

(<><>) : a -> a -> a

(.>) : a -> a

x : a -> a
x y = .> y <><> .> y
