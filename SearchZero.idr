import Language.Reflection

search' : Elaboration m => (0 ty : Type) -> m (Maybe ty)
search' ty = catch $ check {expected = ty} `(%search)

scr : ty -> ty -> Elab ty
scr l r = do
  Just x <- search' $ Semigroup ty
    | Nothing => pure l
  pure $ l <+> r

%language ElabReflection

X : Nat
X = %runElab scr 5 6

xCorr : X = 5
xCorr = Refl

Y : List Nat
Y = %runElab scr [1, 2, 3] [4, 5]

yCorr : Y = [1, 2, 3, 4, 5]
yCorr = Refl
