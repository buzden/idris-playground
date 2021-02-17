g1 : Nat -> Nat
g1 x = 5
--g1 _ = 6

g2 : (Nat, Nat) -> Nat
g2 (x, y) = x
--g2 (a, b) = 6

g3 : (Nat, Nat) -> Nat
g3 (x, y) = x
g3 _ = 6

f : Monad m => m (Nat, Nat)

h2 : Monad m => m Nat
h2 = do
  (x, y) <- f
  --  | (a, b) => pure 5
  pure x

h3 : Monad m => m Nat
h3 = do
  (x, y) <- f
    | _ => pure 5
  pure x
