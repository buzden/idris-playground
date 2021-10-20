-- Case-typed argument is defined in `TTImp` as an intermediate function applied to *all* previous arguments
-- (disregarding whether there exists an actual dependency of not).
-- The follolwing check ensures that those types being applied to different count of arguments mean the same type.

x : {a : Type} -> (xs : List a) -> (v : List a) -> (0 _ : case v of [] => Unit; (x::xs) => Void) -> Nat
y : {a : Type} ->                  (v : List a) -> (0 _ : case v of [] => Unit; (x::xs) => Void) -> Nat

xy : {a : Type} -> (xs : List a) -> (v : List a) -> (0 c : case v of [] => Unit; (x::xs) => Void) -> x {a} xs v c = y {a} v c
