%default total

%tcinline
F : Bool -> Type -> Type
F b x = case b of
          True  => Lazy x
          False => x

data X : Type where
  Nil  : X
--  (::) : Nat -> F b X -> X
  (::) : Nat -> {0 b : Bool} -> (case b of
          True  => Lazy X
          False => X) -> X
