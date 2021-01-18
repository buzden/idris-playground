data X = A Int

(.la) : X -> Int
(.la) (A x) = x

f : X -> String
f x = show x.la
