module RunElabNoEscape

import Language.Reflection

%language ElabReflection

escScr : Elab $ (0 _ : a) -> a
escScr = check $ ILam EmptyFC M0 ExplicitArg (Just `{x}) `(a) `(x)

esc : (0 _ : a) -> a
esc = %runElab escScr

escDecl : Name -> Elab Unit
escDecl name = declare [
                 IDef EmptyFC name [
                   PatClause EmptyFC
                     -- lhs
                     (IApp EmptyFC (IVar EmptyFC name) (IBindVar EmptyFC "x"))
                     -- rhs
                     `(x)
                 ]
               ]

0 esc' : (0 _ : a) -> a

%runElab escDecl `{esc'}

%runElab escDecl `{esc}
