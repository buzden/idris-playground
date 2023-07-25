import Language.Reflection

%language ElabReflection

Ty : Elab Type
Ty = check $ IAlternative EmptyFC FirstSuccess
  [ `(Nat -> Nat)
  , `(String -> String)
  ]

f : %runElab Ty

x : Nat
x = f 5

--s : Nat
--s = f "Wow"
