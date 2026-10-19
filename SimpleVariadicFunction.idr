%default total

interface Param a where
  toString : a -> String

Param String where
  toString = id

Param Nat where
  toString = show

Param Integer where
  toString = show

interface X t where
  fun : List String -> t

Param a => (sub : X s) => X (a -> s) where
  fun acc p = fun @{sub} $ toString p :: acc

X (List String) where
  fun = id

variadic : X t => t
variadic = fun []

res : List String
res = variadic (the String "ft") (the Nat 42)

res2 : List String
res2 = variadic "ft" 42
