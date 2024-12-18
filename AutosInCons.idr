data X : Type -> Type where
  MkX : Eq a => a -> a -> X a

data Z : Type where
  MkZ : Z

data Y : X a -> Type

%hint
EqFromY : Y {a} x => Eq a

data Y : X a -> Type where
  YNat : (x : Nat) -> Y $ MkX x x
  YA : Eq a => {0 x, y : a} -> Y $ MkX x y
  YZ : Eq Z => Y $ MkX MkZ MkZ
  YR : {0 x : X a} -> (y : Y x) -> {x, z : a} -> Y $ MkX x z
