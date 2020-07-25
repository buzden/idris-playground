module Let0

import Data.Nat
import Data.Vect

go : (_ : Vect n elem) -> (_ : Vect m elem) -> Vect (n + m) elem
go         acc []        = let 0 prf = plusZeroRightNeutral n in ?rhs
go {m=S m} acc (x :: xs) = rewrite sym $ plusSuccRightSucc n m in go (x::acc) xs
