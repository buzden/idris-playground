module IHateParens

import Data.List

%default total

infixl 0 .|

-- Instead of `f (a b) $ c d` or `f (a b) (c d)` you can write `f .| a b .| c d`
public export %inline
(.|) : (a -> b) -> a -> b
(.|) = id

f : String -> List String -> String
f x = foldr .| (++) . (++ "_") .| "foo" ++ x
--f x = foldr ((++) . (++ "_")) $ "foo" ++ x
--f x = foldr ((++) . (++ "_")) ("foo" ++ x)

f_corr : f "x" ["a", "b", "c"] = "a_b_c_foox"
f_corr = Refl

record Rec where
  constructor MkRec
  oneField : Int
  anotherField : Nat
  yetAnotherField : List Nat

r : Nat -> Rec
r n = MkRec
  .| cast (n + 1)
  .| n + 3
  .| replicate n 5

r_corr : r 4 = MkRec 5 7 [5, 5, 5, 5]
r_corr = Refl
