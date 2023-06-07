import Language.Reflection

%language ElabReflection

scr : Elab Unit
scr = fail "Show mustn't go on"

vd : Lazy Unit
vd = delay $ %runElab scr

v : Lazy Unit
v = %runElab scr

scr' : Elab $ Lazy Unit
scr' = fail "Show mustn't go on"

vd' : Unit
vd' = force $ %runElab scr'

v' : Unit
v' = %runElab scr'
