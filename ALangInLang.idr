import Language.Reflection

data MyLangExpr = AName String | AnApp MyLangExpr Nat

parseMLE : TTImp -> Elab $ Either (FC, String) MyLangExpr
parseMLE (IVar fc $ UN $ Basic n) = pure @{Compose} $ AName n
parseMLE (IVar fc nm)             = pure $ Left $ (fc, "Expected a plain name, got `\{show nm}`")
parseMLE (IApp fc s t)            = do lhs <- parseMLE s
                                       rhs <- check t <|> failAt (getFC t) "Expected a `Nat` expression, got `\{show t}`"
                                       pure [| AnApp lhs (pure rhs) |]
parseMLE expr = pure $ Left (getFC expr, "Expected a name or an application, got `\{show expr}`")

%TTImpLit fromTTImp

%macro
fromTTImp : TTImp -> Elab MyLangExpr
fromTTImp = either (uncurry failAt) pure <=< parseMLE

ok1 : MyLangExpr
ok1 = `(aName)

failing "Expected a `Nat` expression, got `anArg`"

  bad : MyLangExpr
  bad = `(aNameApplied anArg)

ok2 : Nat -> MyLangExpr
ok2 anArg = `(aNameApplied anArg)

ok3 : Nat -> MyLangExpr
ok3 anArg = `(aNameApplied $ 4 + 5)

ok4 : MyLangExpr
ok4 = `(4 + 4)

failing "Expected a plain name, got `.postfixName`"

  bad : MyLangExpr
  bad = `(4.postfixName)

failing "Expected a name or an application, got `let x :"

  bad : MyLangExpr
  bad = `(let x = 4 in x + 5)
