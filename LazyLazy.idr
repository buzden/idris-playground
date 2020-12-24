module LazyLazy

import Data.List.Lazy

%default total

coef : Nat
coef = 50000

level3 : LazyList Nat
level3 = iterateN coef (+1) 0 >>= replicate coef >>= replicate coef

main : IO ()
main = putStrLn $ show $ head' level3
