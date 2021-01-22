x : IO $ Either Bool $ Maybe Bool

f : IO ()
f = do
  Left b <- x
    | Right (Just b) => pure ()
     | Right Nothing => pure ()
  pure ()
