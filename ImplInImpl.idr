%default total

data X : Nat -> Type where
  MkX : X n

data Y : (vs : X n) -> Type where
  MkY : Y vs

data Z : Y vs -> Type where
  MkZ0 : Z y         -- works
  MkZ1 : Nat -> Z y  -- error
