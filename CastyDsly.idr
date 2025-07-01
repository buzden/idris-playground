module CastyDsly

import Data.DPair

import Language.Reflection

%default total

data Expr : Type -> Type where
  S : String -> Expr a
  X : a -> Expr a
  O : Expr a -> Expr a -> Expr a

cleanupNamedHoles : TTImp -> TTImp
cleanupNamedHoles = mapTTImp $ \case
  IHole {} => Implicit EmptyFC False
  e        => e

tryAll : List (Exists $ \t => t -> a) -> TTImp -> Elab a
tryAll []                 e = failAt (getFC e) "Argument is not a well-formed expression"
tryAll (Evidence t f::xs) e = case !(catch $ check {expected=t} e) of
  Just x  => pure $ f x
  Nothing => tryAll xs e

tryCast : t -> Elab $ Expr a
tryCast x = tryAll [Evidence (Expr a) id, Evidence String S, Evidence a X] $ cleanupNamedHoles !(quote x)

%macro
op : l -> r -> Elab $ Expr a
op x y = pure $ O !(tryCast x) !(tryCast y)

x : Expr Nat
x = "lala" `op` Z

y : Expr Double
y = 1.5 `op` "alal"

z : Expr Double
z = "lala" `op` y

z' : Expr Double
z' = "lala" `op` (1.5 `op` "alal")
