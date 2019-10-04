module ErrNList

import Effect.Exception
import Effect.Select
import Effects

data Error = NumberIs2

f : Int -> Eff Int [SELECT, EXCEPTION Error]
f n = do
    x <- select [n .. 10]
    if x == 2
        then raise NumberIs2
        else pure x

m : Maybe Int
m = run $ f 3

l : List Int
l = run $ f 3

el : List (Either Error Int)
el = run $ f 3

le : Either Error (List Int)
le = run $ f 3
