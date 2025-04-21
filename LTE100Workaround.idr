import Data.Nat

%default total

ind2 : (0 t : Nat -> Nat -> Type) -> (forall n, m. t n m -> t (S n) (S m)) -> (k : Nat) -> t n m -> t (k+n) (k+m)
ind2 t f 0     x = x
ind2 t f (S k) x = f (ind2 t f k x)

%hint
Workaround : LTE a b => LTE (100+a) (100+b)
Workaround @{prf} = ind2 LTE LTESucc 100 prf

x : LTE 512 2048
x = %search
