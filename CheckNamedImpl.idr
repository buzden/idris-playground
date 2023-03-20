import Data.Maybe

import Language.Reflection

%language ElabReflection

checker : (k -> Type) -> k -> Name -> Elab Bool
checker ty v name = map isJust $ catch $ check {expected=ty v} $ IVar EmptyFC name

ForAny : Bool
ForAny = %runElab checker Semigroup (Lazy Bool) `{Any}

forAnyTrue : ForAny = True
forAnyTrue = Refl

ForAnyy : Bool
ForAnyy = %runElab checker Semigroup (Lazy Bool) `{Anyy}

forAnyyFalse : ForAnyy = False
forAnyyFalse = Refl
