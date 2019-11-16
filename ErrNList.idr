module ErrNList

import Effect.Select
import Effect.StdIO
import Effects

f : Int -> Eff Int [SELECT, STDIO]
f n = do
    x <- select [n .. 10]
    if x == 2
        then do
          putStrLn "The number is 2, incrementing"
          pure $ x + 1
        else pure x

-- m : Maybe Int
-- m = run $ f 3

-- l : List Int
-- l = run $ f 3

el : List (IO Int)
el = run . run $ f 3

el' : List (IO Int)
el' = run $ f 3

le : IO (List Int)
le = run . run $ f 3

le' : IO (List Int)
le' = run $ f 3
