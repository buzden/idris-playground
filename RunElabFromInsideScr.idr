module RunElabFromInsideScr

import Language.Reflection

%default total
%language ElabReflection

%macro
f : Elab Nat
f = logMsg "wow" 0 "yay!" $> 5

g : Elab ()
g = declare $ pure $ IDef EmptyFC `{zz} $ pure $ PatClause EmptyFC `(zz) `(3 + f)

%runElab g

zz_corr : RunElabFromInsideScr.zz = 8
zz_corr = Refl
