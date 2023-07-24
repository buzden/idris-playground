import Language.Reflection

%language ElabReflection

decl : Elab ()
decl = declare `[
    %macro
    fun : Elab Nat
    fun = pure 5
  ]

failing
  x : Nat
  x = fun

%runElab decl

x : Nat
x = fun
