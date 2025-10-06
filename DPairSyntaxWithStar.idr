import Data.Vect

%hide Prelude.Ops.infixl.(*)
export typebind infixr 0 *

(*) : (a : Type) -> (a -> Type) -> Type
(*) = DPair

aPair : (n : Nat) * Vect n Nat
aPair = (_ ** [1, 2, 3, 4, 5])
