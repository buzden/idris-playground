module CanEscape

import Language.Reflection

%language ElabReflection

-- Show that actually an erased value can escape through an elaboration script

0 n : Nat
n = 3

elabScript : Elab Nat
elabScript = check !(quote n)

M : Nat
M = %runElab elabScript

mIs3 : M = 3
mIs3 = Refl
