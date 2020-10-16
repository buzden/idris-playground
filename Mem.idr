module Mem

import Data.Vect

-- Effectively (size : Nat ** Vect size a)
record Region a where
  constructor MkRegion
  regionSize : Nat
  regionData : Vect regionSize a

-- Effectively (regs : Nat ** Vect regs (Region a))
record RegionsOfType a where
  constructor MkRegOfType
  regionCnt : Nat
  regionsOfType : Vect regs $ Region a

record Memory where
  constructor MkMemReg
  regionsByType : (a : Type) -> RegionsOfType a

record Pointer where
  constructor MkPointer
  type : Type
  regionNum : Nat
  idxInRegion : Nat

data CorrectPointer : Pointer -> Memory -> Type where
