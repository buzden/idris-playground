module CantElabType

import Data.Vect

import Language.Reflection

%language ElabReflection

0 T : Nat -> Type
T n = Vect n Nat

desiredType : TTImp
desiredType = IApp EmptyFC (IVar EmptyFC `{CantElabType.T}) `(3)

elabDecl : Name -> Elab Unit
elabDecl n = declare [
    IClaim EmptyFC MW Public [] $ MkTy EmptyFC EmptyFC n desiredType
  ]

%runElab elabDecl `{x1}
x1 = [1, 2, 3]

elabExpr : Elab Type
elabExpr = check desiredType

-- should typecheck because the rig of calling is zero

x2 : %runElab elabExpr
x2 = [1, 2, 3]

-- check that zero does not leak, should not typecheck

T' : Type
T' = %runElab elabExpr
