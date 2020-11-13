module StructuralEquivalents

import Data.DPair
import Data.Nat

namespace Equivalence

  data Singleton : a -> Type where
    Val : (x : a) -> Singleton x

  NonStruct : {a : Type} -> a -> Type
  NonStruct x = Subset a (\y => y = x)

  -- Without respect to zero quantity of the bound
  Rougher : {a : Type} -> a -> Type
  Rougher x = (y : a ** y = x)

namespace BoundedNats

  data Fin : Nat -> Type where
    FZ : Fin n
    FS : Fin n -> Fin $ S n

  NonStruct : Nat -> Type
  NonStruct n = Subset Nat (`LT` n)

  -- Without respect to zero quantity of the bound
  Rougher : Nat -> Type
  Rougher n = (x : Nat ** x `LT` n)
