module Mb

import public Language.Reflection.Pretty
import public Language.Reflection.Syntax
import public Language.Reflection.Types
import Data.Vect

%language ElabReflection

export
maybeInfo : TypeInfo
maybeInfo = getInfo "Maybe"

data T : Type -> Type where
  TU : T Unit
  TI : T Int
  Ta : T a

tParamInfo : ParamTypeInfo
--tParamInfo = getParamInfo "T"

data P : Nat -> Type where
  PZ : P Z
  PS : (x : Nat) -> P (S x)
  P3 : (y : Nat) -> P (S y)

data Q : Nat -> Type where
  QZ : Q Z
  QS : (x : Nat) -> Q (S x)
  Q3 : (xs : List Nat) -> Q (S $ length xs)

data R : Nat -> Type where
  RZ  : R Z
  RS  : (x : Nat) -> R (S x)
  RSS : (y : Nat) -> R (S (S y))

pParamInfo : ParamTypeInfo
--pParamInfo = getParamInfo "P"

qParamInfo : ParamTypeInfo
--qParamInfo = getParamInfo "Q"

rParamInfo : ParamTypeInfo
--rParamInfo = getParamInfo "R"
