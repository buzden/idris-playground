module ElabImplLambda

import Language.Reflection

%language ElabReflection

derive : {ty : Type} -> Elab ty
derive = check $
           ILam EmptyFC MW ExplicitArg (Just `{x}) `(Nat) $
             ILam EmptyFC MW AutoImplicit Nothing `(List Nat) $
               `(x + 1)

derived : Nat -> List Nat => Nat
derived = %runElab derive
