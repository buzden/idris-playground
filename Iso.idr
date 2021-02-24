--module Data.Iso
module Iso

import Data.DPair
import Data.Nat
import Data.Fin
import Data.Fin.Extra

import Syntax.WithProof

%default total

-- TODO to think of weaker form of isomorphism:
--  0 to_from_to_is_from : (x : a) -> to (from (to x)) = to x
--  0 from_to_from_is_to : (y : b) -> from (to (from y)) = from y

infix 0 =~=

public export
interface (=~=) a b where
  constructor MkIso

  to   : a -> b
  from : b -> a

  0 from_to_id : (x : a) -> from (to x) = x
  0 to_from_id : (y : b) -> to (from y) = y

public export
(=~=) (Fin n) (Subset Nat (`LT` n)) where
  to {n=S k} FZ = Element Z (LTESucc LTEZero)
  to (FS x)     = bimap S LTESucc $ to x

  from = uncurry natToFinLTE

  from_to_id FZ = Refl
  from_to_id {n=S k} (FS x) with (from_to_id {b=Subset Nat (`LT` k)} x)
    from_to_id (FS x) | fti with (to {b=Subset Nat (`LT` k)} x)
      from_to_id (FS x) | fti | Element fst snd = rewrite fti in Refl

  to_from_id (Element Z (LTESucc LTEZero)) = Refl
  to_from_id {n=S n} (Element (S k) (LTESucc x)) = rewrite to_from_id {a=Fin n} {b=Subset Nat (`LT` n)} (Element k x) in Refl
  to_from_id (Element (S k) LTEZero) impossible
