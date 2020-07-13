module Goldbach

import Data.DPair
import Data.Nat

public export
data Even : Nat -> Type where
  EvZ  : Even Z
  EvSS : Even n -> Even $ S $ S n

public export
half : (n : Nat) -> {auto ev : Even n} -> Subset Nat (\k => n = k + k) -- like `(k ** n = k + k)` but with compile-time right argument.
half Z = Element Z Refl
half (S $ S k) {ev=EvSS _} = let Element halfK halfKPrf = half k in
                             Element (S halfK) rewrite sym $ plusSuccRightSucc halfK halfK in
                                               rewrite halfKPrf in
                                               Refl

export
gte1nz : (k : Nat) -> {auto gte : k `GTE` S x} -> Not (k = 0)
gte1nz 0     Refl impossible
gte1nz (S _) Refl impossible

public export
Prime : Nat -> Type
Prime n = (k : Nat) -> {auto gt2 : k `GTE` 2} -> {auto ltn : k `LT` n} -> Not (modNatNZ n k (gte1nz k {x=1}) = 0)

export
goldbach : (x : Nat) -> {auto ev : Even x} -> {auto gt2 : x `GT` 2} -> (y ** z ** (Prime y, Prime z, x = y + z))
