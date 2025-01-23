data NotEq : (a, b : Nat) -> Type where
  ZS : NotEq Z (S n)
  SZ : NotEq (S n) Z
  SS : NotEq n m -> NotEq (S n) (S m)

fwd : NotEq n m -> Not (n = m)
fwd (SS x) Refl = fwd x Refl

bck : {n, m : Nat} -> Not (n = m) -> NotEq n m
bck {n = Z}   {m = Z}   f = absurd $ f Refl
bck {n = Z}   {m = S k} f = ZS
bck {n = S k} {m = Z}   f = SZ
bck {n = S k} {m = S j} f = SS $ bck $ \case Refl => f Refl
