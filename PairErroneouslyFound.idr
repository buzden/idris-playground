data X = MkX

useX : X => Nat

v : (X, String)

f : Nat
f = do
  let (x, _) = v
  useX

f' : Nat
f' = do
  let xx = v
  useX

g : Nat
g = do
  let xx@(x, _) = v
  useX

g' : Monad m => m Nat
g' = do
  (x, _) <- pure v
  pure useX

g'' : Monad m => m Nat
g'' = do
  xx@(x, _) <- pure v
  pure useX
