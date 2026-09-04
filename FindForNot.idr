import Data.Vect

import Language.Reflection

data Arg : Type

interface DerivSubst (0 a : Type) where
  substArgsCount : Nat
  substArgsCount = 1
  argsInstead : Vect substArgsCount Arg
  substitution : Vect substArgsCount Name -> TTImp

DerivSubst (Not $ a === b) where
  argsInstead = [?foo_arg]
  substitution [n] = `(lalala)

X : Type
X = True = False -> Void

x_impl : DerivSubst X
x_impl = %search

Y : Type
Y = Nat = False -> Void

y_impl : DerivSubst Y
failing
  y_impl = %search
