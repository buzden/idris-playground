import Language.Reflection

export %macro
nameStr : Type -> Elab String
nameStr ty = check !(quote $ show !(quote ty))
  -- requoting after `show` because `Show Name` is not `public export`

N : String
N = nameStr Nat

N_corr : N = "Prelude.Types.Nat"
N_corr = Refl

LN : String
LN = nameStr $ List Nat

LN_corr : LN = "Prelude.Basics.List Prelude.Types.Nat"
LN_corr = Refl
