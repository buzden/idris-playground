import Data.Vect

import Language.Reflection

%language ElabReflection

%default total

innerScript : Elab Nat
innerScript = pure 5

failing "Can't reflect a %runElab"
  outerScript : Elab Type
  outerScript = check `(Vect (%runElab innerScript) Nat)

declareX : Elab ()
declareX = declare `[
    x : Nat
    x = 5
  ]

declareDeclareX : Elab ()
declareDeclareX = declare $ pure $ IRunElabDecl EmptyFC `(declareX)

failing "Can't reify as Decl"
  %runElab declareDeclareX
