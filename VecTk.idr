module VecTk

import Data.Vect
import Data.Fin

tk : (k : Nat) -> Vect (k + n) a -> Vect n a
tk Z xs = xs
tk (S k) (x::xs) = tk k xs
