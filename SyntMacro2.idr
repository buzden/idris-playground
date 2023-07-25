import Language.Reflection

%language ElabReflection

%hide Prelude.(.)

infixr 0 `try`

-- %macro %inline %tcinline
(.) : Elab a
(.) = do
  let expr = `(\f, g, x => f (g x))
  (do Refl <- check {expected=(a = (forall a, b, c. (b -> c) -> ((0 _ : a) -> b) -> (0 _ : a) -> c))} `(Refl)
      check expr
    ) `try`
  (do Refl <- check {expected=(a = (forall a, b, c. ((0 _ : b) -> c) -> (a -> b) -> (0 _ : a) -> c))} `(Refl)
      check expr
    ) `try` fail "unable to find an appropriate type"

irsx : (0 _ : a = b) -> b = a
irsx = (%runElab (.)) irrelevantEq sym

--irsx' : (0 _ : a = b) -> b = a
--irsx' x = sym . irrelevantEq $ x

--irs : (0 _ : a = b) -> b = a
--irs = irrelevantEq . sym
--
--irs' : (0 _ : a = b) -> b = a
--irs' = sym . irrelevantEq
