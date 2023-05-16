ff : (n, k : Nat) -> k = n + 1 -> Nat
ff n .(n + 1) Refl = 4

ff' : (k, n : Nat) -> k = n + 1 -> Nat
ff' .(n + 1) n Refl = 4

--

ff_ : (n, k : Nat) -> k = n + 1 -> Nat
ff_ n k r with (())
  ff_ n (n + 1) Refl | () = 4

ff'_ : (k, n : Nat) -> k = n + 1 -> Nat
ff'_ k n r with (())
  ff'_ (n + 1) n Refl | () = 4

--

{-

ffg : (f : Nat -> Nat) -> (k, n : Nat) -> (if k > 5 then n = f 5 else n = 5) -> Nat
ffg f k n prf with (k > 5)
  ffg f k .(f 5) Refl | True = ?foo_t
  ffg f k n prf | False = ?foo_f

fff : (f : Nat -> Nat) -> (k, n : Nat) -> (if k > 5 then n = (if f k < 8 then 1 else 0) else n = 5) -> Nat
fff f k n prf with (k > 5)
  fff f k .(if f k < 8 then 1 else 0) Refl | True = ?foo_t
  fff f k n prf | False = ?foo_f
