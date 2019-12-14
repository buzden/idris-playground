module Dollar

infixr 1 $
($) : Int -> Int -> Int
($) u x = x + 1

f : Int -> Int
f x = x $ 5
