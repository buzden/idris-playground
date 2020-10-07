module IntegerThruNat

%default total

------------------------------------------------------------------------

namespace Bad1

  -- One example of bad integer definition
  public export
  data Intege = MkInteger (Bool, Nat)

  -- `MkInteger (True, 0)` effectively equal to `MkInteger (False, 0)`
  -- but functions need to match both

------------------------------------------------------------------------

namespace Bad2

  public export
  data Intege = Zero
              | Pos Nat
              | Neg Nat

  -- `Pos 0` meaning zero is bad by the same reason as the example above.

  -- But we can say that `Pos n` means effectively `n + 1` and `Neg n` means effectively `n - 1`.

  export
  div : Intege -> Intege -> Maybe Intege
  div _ Zero = Nothing
  div Zero _ = Just Zero
  div (Pos x) (Pos y) = Just $ Pos ?pospos
  div (Neg x) (Neg y) = Just $ Pos ?negneg
  div (Pos x) (Neg y) = Just $ Pos ?posneg
  div (Neg x) (Pos y) = Just $ Pos ?negpos

  -- Then everything is okay during the match except it's inconvenient:

  export
  abs : Intege -> Nat
  abs Zero = Z
  abs (Pos x) = S x
  abs (Neg x) = x -- F*CK! It's tempting to forget to add `S` when using matched `Nat`

------------------------------------------------------------------------

namespace AsIf

  -- What we can do (at least, as I thought) in Arend (shown with non-existent Idris syntax) --

--  data Intege = Zero
--              | Pos Nat with | Pos 0 => Zero
--              | Neg Nat with | Neg 0 => Zero

  -- Here `Pos 0` means zero and is literally equal to `Zero`. And to the `Neg 0` too.
  -- During the pattern match we can match on `Zero`, `Pos x` (including x=0) or both as we want.

--  div : Intege -> Intege -> Maybe Intege
--  div _ Zero = Nothing
--  div Zero _ = Just Zero
--  div (Pos (S x)) (Pos (S y)) = ...
--  ... etc ...
    -- Here ^^^^^^^ we can match `Pos x`, but since the case of `Zero` is already matched, we can match just `Pos (S x)`.

--  abs : Intege -> Nat
--  abs (Pos x) = x
--  abs (Neg x) = x
    -- Here ^^^ we even don't match `Zero` because it's covered by both cases.
    -- And compiler would check that `Pos 0` and `Neg 0` cases would give the same result.
    -- So `abs (Neg x) = S x` won't typecheck.

------------------------------------------------------------------------

namespace Ersatz

  -- Let's have the same meaning as we wanted (i.e. `Pos 0` and `Neg 0` are effectively `Zero`)

  public export
  data Intege = Zero
              | Pos Nat
              | Neg Nat

  -- But let's define equivalences as a separate function!

  public export
  0 intege : Intege -> Intege
  intege (Pos 0) = Zero
  intege (Neg 0) = Zero
  intege x = x

  public export
  abs : Intege -> Nat
  abs (Pos x) = x
  abs (Neg x) = x
  abs Zero = 0 -- still need to match it

  export
  0 abs_holds_equiv : (n : Intege) -> abs n = abs (intege n)
  abs_holds_equiv Zero        = Refl
  abs_holds_equiv (Pos Z)     = Refl
  abs_holds_equiv (Pos $ S _) = Refl
  abs_holds_equiv (Neg Z)     = Refl
  abs_holds_equiv (Neg $ S _) = Refl

  -- But this should be repeated for each function (and matching should go for each argument). It could be done automatically.
  -- In the automatic variant, equivalence function could be partial meaning that it's identity on those inputs that it's not defined on.

  -- Also, covering check needs to be modified in this case to make able to not to write redundant cases.

  -- Well, can this mechanism we implemented with Idris elaborations?
