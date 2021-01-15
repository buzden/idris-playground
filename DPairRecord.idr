import Data.Vect

someVect : (n ** Vect n Int)
-- someVect = (_ ** [])

someVectLen : Nat
someVectLen = someVect.fst
