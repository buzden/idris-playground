module Conat

%default total

namespace R

  record Conat where
    constructor C
    pred : Maybe $ Inf Conat

  Z : Conat
  Z = C {pred = Nothing}

  S : Conat -> Conat
  S n = C {pred = Just n}

  -- Infinity value
  I : Conat
  I = C {pred = Just I}

  coind : (p : Conat -> Type) -> p Z -> ({n : Conat} -> p (S n) -> p n) -> (n : Conat) -> Inf (p n)
  coind p base _    (C Nothing)    = base
  coind p base prev n@(C $ Just _) = prev {n} $ coind p base prev $ S n

namespace D

  %hide Prelude.Z
  %hide Prelude.S

  %hide Conat.R.Conat
  %hide Conat.R.Z
  %hide Conat.R.S

  data Conat : Type where
    Z : Conat
    S : Inf Conat -> Conat

  I : Conat
  I = S I

  coind : (p : Conat -> Type) -> p Z -> ({n : Conat} -> p (S n) -> p n) -> (n : Conat) -> Inf (p n)
  coind p base _    Z       = base
  coind p base prev n@(S _) = prev {n} $ coind p base prev $ S n
