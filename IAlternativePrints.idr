import Language.Reflection

%language ElabReflection
%default total

magicScript : Elab a
magicScript = check $ IAlternative EmptyFC FirstSuccess
  [ `(the Nat 5)
  , `(the String "foo")
  ]

x : Nat
x = %runElab magicScript

y : String
y = %runElab magicScript

-- Should print both attempts in the error message
z : Bool
z = %runElab magicScript
