import Text.PrettyPrint.Bernardy

%default total

x : {opts : _} -> Doc opts
x = vsep
  [ "one"
  , "two"
  , "three"
  ]

y : {opts : _} -> Doc opts
y = vsep
  [ "12"
  , "286"
  ]

s : String
s = render (Opts 152) $ x <+> y

s' : String
s' = render (Opts 152) $ x <++> y

private infixl 8 <+?+>

(<+?+>) : {opts : _} -> Doc opts -> Doc opts -> Doc opts
x <+?+> y = do
  l <- x
  if width l == 0 then y else do
    r <- y
    if width r == 0 then pure l else
      pure l <+> space <+> pure r

s'' : String
s'' = render (Opts 152) $ x <+?+> y

es' : String
es' = render (Opts 152) $ x <++> empty <++> y

es'' : String
es'' = render (Opts 152) $ x <+?+> empty <+?+> y

main : IO ()
main = do
  putStrLn s
  putStrLn "---"
  putStrLn s'
  putStrLn "---"
  putStrLn s''
  putStrLn "---"
  putStrLn "---"
  putStrLn es'
  putStrLn "---"
  putStrLn es''
