import Data.Nat

%default total

export infix 0 `po`, `po'`

export typebind infixr 0 `op`, `op'`

op, po : (mty : Type) -> (ty -> Type) -> Type

g : Maybe Nat `po` \res => 5 `LT` res
f : (res : Maybe Nat) `op` (5 `LT` res)

op', po' : (mty : Type) -> (mty = Maybe ty) => (ty -> Type) -> Type

g' : Maybe Nat `po'` \res => 5 `LT` res
f' : (res : Maybe Nat) `op'` (5 `LT` res)
