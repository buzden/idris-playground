import Language.Reflection

%default total

%language ElabReflection

x : Void -> a
--x _ impossible
%runElab declare $ pure $ IDef EmptyFC `{x} []

aHole : Void

main : IO ()
main = putStrLn $ x aHole
