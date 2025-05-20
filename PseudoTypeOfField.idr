import Data.Fin

%default total

0 recFieldType : (a : Type) -> (a -> b) -> Type
recFieldType _ _ = b

0 recValFieldType : (x : a) -> (a -> b) -> Type
recValFieldType _ _ = b

record Rec where
  field1 : Nat
  field2 : Integer
  field3 : Fin field1

rec : Rec

x : recFieldType Rec (.field1)
x = 5

y : recValFieldType rec (.field1)
y = 6
