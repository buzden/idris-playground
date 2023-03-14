data E = MkE Unit

data P : E -> Type where

data X : E -> Type

empty : X $ MkE ()

mk : P a => X a -> X b

failing "Mismatch between: Nat and ()"

  foofu : Nat -> X a
  foofu n = mk $
    case n of
      Z => empty
      _ => ?foo_1
