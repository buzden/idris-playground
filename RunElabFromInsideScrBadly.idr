module RunElabFromInsideScrBadly

import Language.Reflection

%default total
%language ElabReflection

%macro
f : Elab Nat
f = do
  n <- genSym "x"
  logMsg "haha" 0 "before declaring inside `f` %macro"
  declare $ pure $ IDef EmptyFC n $ pure $ PatClause EmptyFC (IVar EmptyFC n) `(3 + f)
  pure 5

x : Nat
x = f
