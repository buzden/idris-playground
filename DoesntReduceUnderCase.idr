v : (Nat, Nat)

g : Unit
g = do
  let xx@(x, _) = v
  let prf1 = the (fst xx = x) Refl
  let _ = case () of
            _ => do
              let prf2 = the (fst xx = x) Refl
              ()
  ()
