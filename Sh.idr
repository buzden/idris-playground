import Language.Reflection

%default total

elimHoleApp : TTImp -> TTImp
elimHoleApp $ IApp      _ s   $ IHole {} = s
elimHoleApp $ INamedApp _ s _ $ IHole {} = s
elimHoleApp $ IAutoApp  _ s   $ IHole {} = s
elimHoleApp $ IWithApp  _ s   $ IHole {} = s
elimHoleApp x = x

%macro
s : a -> Elab a
s x = do
  e <- quote x
  let e = mapTTImp elimHoleApp e
  logMsg "elab" 0 $ show e
  check e -- pure x

x : List Nat
x = s $ [1, 2, 3] >>= pure . S

x_corr : Main.x = [2, 3, 4]
x_corr = Refl
