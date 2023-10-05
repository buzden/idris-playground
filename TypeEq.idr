import Language.Reflection

%language ElabReflection

%macro
(==) : Type -> Type -> Elab Bool
x == y = pure $ !(quote x) == !(quote y)

trueExample : Nat == Nat = True
trueExample = Refl

falseExample : Nat == List Nat = False
falseExample = Refl
