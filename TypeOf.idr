module TypeOf

import Language.Reflection

%default total

%macro
TypeOf : a -> Elab Type
TypeOf _ = check =<< quote a

x : Nat -> String

y : (xx : TypeOf TypeOf.x) -> String
y xx = ?foo
