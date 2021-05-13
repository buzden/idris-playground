module InfoWithImplicit

import public Language.Reflection.Pretty
import public Language.Reflection.Syntax
import public Language.Reflection.Types
import Data.Vect

import Mb

%language ElabReflection

data X : Vect n a -> Type where
  XX : X []

export
inf : TypeInfo
inf = getInfo "X"

export
mbInf : TypeInfo
mbInf = getInfo "T"
-- `T` and its constructors are visible even when they are not exported
