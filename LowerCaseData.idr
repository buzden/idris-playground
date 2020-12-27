module LowerCaseData

%default total

data TeXNat = zero | succ TeXNat
dts : TeXNat -> String
dts n = case n of
  LowerCaseData.zero   => "zero"
  LowerCaseData.succ _ => "non-zero"
