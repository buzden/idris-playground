module LazyLazy

import Data.List as L
import Data.List.Lazy

%default total

coef : Nat
coef = 10000

longId : Nat -> Nat
longId n = foldr max n $ L.replicate n n

level3 : LazyList Nat
level3 = iterateN coef (+1) 0 >>= replicate coef . longId >>= replicate coef . longId

main : IO ()
main = putStrLn $ show $ head' level3
