import Language.Reflection

%default total

%language ElabReflection

e : Nat -> Elab String
e n = logMsg "de.num" 0 "\{show n}" $> "n\{show n}"

s : String -> Elab String
s st = logMsg "de.str" 0 st $> st ++ "."

f : Nat -> Elab $ IO Unit
f = e >=> map putStrLn . s

main : IO Unit
main = %runElab sequence_ <$> traverse f [10, 20, 12]
