import Language.Reflection

%language ElabReflection

shouldNotFail : Elab ()
shouldNotFail = do
  try (ignore $ check {expected=Nat} `("a string")) (pure ())
  try (declare `[x : Nat; x = "a string"]) (pure ())

%runElab shouldNotFail
