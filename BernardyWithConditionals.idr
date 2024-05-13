import Text.PrettyPrint.Bernardy

%default total

w : Bool -> Doc opts -> Doc opts
w b = if b then id else const empty

x : {opts : _} -> Doc opts
x = vsep
  [ "if" <++> w False "{"
  , "if" <++> w True "}"
  , w True "}" <++> "fi"
  , w False "}" <++> "fi"
  ]

y : {opts : _} -> Doc opts
y = vsep
  [ "if" <+> w False " {"
  , "if" <+> w True " }"
  , w True "} " <+> "fi"
  , w False "} " <+> "fi"
  ]

s : String
s = render (Opts 152) x

s' : String
s' = render (Opts 152) y

main : IO ()
main = do
  putStrLn s
  putStrLn "---"
  putStrLn s'
