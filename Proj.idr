data X = A Int

(.la) : X -> Int
(.la) (A x) = x

f : X -> String
f x = show x.la

-- Projection does not define the usual function.
-- `g` does not typecheck without the `la` definition.
-- Moreover, they may have different implementations.

la : X -> Int
la $ A x = x + 1

g : X -> String
g x = show $ la x
