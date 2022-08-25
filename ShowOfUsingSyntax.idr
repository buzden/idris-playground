import Data.Fin

data AA : a -> Type where
  MkAA : AA a

using (zz : Fin 5)

  data X : AA zz -> Type where
    MkX : X MkAA

data X' : AA zz -> Type where
  MkX' : X' MkAA

-- in REPL try
-- :set showimplicits
-- :t X
-- :t X'
