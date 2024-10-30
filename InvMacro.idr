import Language.Reflection

%language ElabReflection
%default total

%runElab declare $ pure $ IClaim EmptyFC MW Public [Invertible] $ MkTy EmptyFC EmptyFC `{F} `({0 a : Type} -> Maybe a)
F = Nothing

f : Maybe a -> Nat
f F = 5
f _ = 6
