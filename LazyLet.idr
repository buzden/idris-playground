import Data.List.Lazy

f : Nat -> (Nat, Nat)
f n = unsafePerformIO $ do
  putStrLn "with \{show n}"
  pure (n+1, n+2)

x : Nat -> (Lazy Nat, Nat)
x n = let (a, b) = f n in
      (delay $ a + b, 1)

y : Nat -> (Lazy Nat, Nat)
y n = let u = f n in
      (delay $ fst u + snd u, 1)

y' : Nat -> (Lazy Nat, Nat)
y' n = let u : (Nat, Nat)
           u = f n in
       (delay $ fst u + snd u, 1)

z : Nat -> (Lazy Nat, Nat)
z n = (delay $ fst (f n) + snd (f n), 1)

-- :exec putStrLn $ show $ snd $ y 4
-- :exec putStrLn $ show $ snd $ y' 4
