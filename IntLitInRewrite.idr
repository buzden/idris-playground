import Data.Nat

data X = MkX

fromInteger : Integer -> X

(+) : X -> X -> X

%default total

conc : List a -> List a -> List a
conc xs []      = xs
conc xs (y::ys) = y :: conc xs ys

concLen : (xs, ys : List a) -> length (xs `conc` ys) = length xs + length ys
concLen xs []      = rewrite plusCommutative (length xs) 0 in Refl
concLen xs (y::ys) = do
  --rewrite plusCommutative (length xs) (1 + length ys)
  let u = plusCommutative (length xs) (1 + length ys)
  rewrite u
  ?dfoo

whatWouldYouLike : Nat
whatWouldYouLike = 4
