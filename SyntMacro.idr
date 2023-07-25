import Language.Reflection

%language ElabReflection

%hide Prelude.(.)

%macro -- %inline %tcinline
(.) : Elab a
(.) = check `(\f, g, x => f (g x))

irs : (0 _ : a = b) -> b = a
irs = irrelevantEq . sym

irs' : (0 _ : a = b) -> b = a
irs' = sym . irrelevantEq
