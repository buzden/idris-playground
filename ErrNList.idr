module ErrNList

import Effect.Exception
import Effect.Select
import Effects

data Error = NumberIs2

f : Int -> Eff Int [EXCEPTION Error, SELECT]
f n = do
    x <- select [n .. 10]
    if x == 2
        then raise E2
        else pure x

el : List (Either Error Int)
el = run f

le : Either Error (List Int)
le = run f