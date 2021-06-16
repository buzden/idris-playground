%default total

%hide Prelude.List

data List : Type -> Type where
  Nil  : List a
  (::) : (1 _ : a) -> (1 _ : List a) -> List a

append : (1 _ : List a) -> (1 _ : List a) -> List a
append []      ys = ys
append (x::xs) ys = x :: append xs ys
