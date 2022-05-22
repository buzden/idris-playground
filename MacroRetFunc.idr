import Language.Reflection

%language ElabReflection

%macro
coolMacro : Nat -> Elab (Nat -> Nat)
coolMacro n = lambda Nat $ \m => pure $ n + m + 1

y : Nat
y = let z = coolMacro 4 in z 5

x : Nat
x = coolMacro 4 5
