import Data.Vect

interface X a where
  x : a -> String

X String where
  x = id

X (List String) where
  x = show

s : String
s = x ["a", "b"]
