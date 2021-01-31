module ColistFun

-- Inspired by a pull request https://github.com/idris-lang/Idris2/pull/997
-- by Stefan Hoeck and by discussion started by Mathew Polzin.

data Colist : Type -> Type where
  Nil  : Colist a
  (::) : a -> Inf (Colist a) -> Colist a

Functor Colist where
  map f []      = []
  map f (x::xs) = f x :: map f xs

functorId : (xs : Colist a) -> map Prelude.id xs = xs
functorId [] = Refl
functorId (x::Delay xs) = cong (x::) $ functorId xs
