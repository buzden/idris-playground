ff : List Nat
ff = let x = 4 in [| x |]

--fg : List Nat
--fg = [| 4 |]
--
--fs : List String
--fs = [| "" |]

fromString : String -> (Nat -> Nat -> Nat)
fromString "haha" = (*)
fromString _      = (+)

--fh : List Nat -> List Nat -> List Nat
--fh a b = [| "haha" a b |]

fh' : List Nat -> List Nat -> List Nat
fh' a b = let x = "haha" in [| x a b |]

prop : fh' [4] [5] = [20]
prop = Refl
