import Language.Reflection

y, z : Nat
y = 4
z = 5

x : Nat
x = 1 + (y + z)

%language ElabReflection

%runElab logSugaredTerm "lsh" 0 "x" !(quote x)
