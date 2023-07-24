import Language.Reflection

%language ElabReflection

%default total

f : Nat -> Nat

scr : Elab ()
scr = declare
  [ IDef EmptyFC `{f}
    [ PatClause EmptyFC `(f Z) `(5)
    ]
  , IDef EmptyFC `{f}
    [ PatClause EmptyFC `(f (S n)) `(5 + n)
    ]
  ]

%runElab scr
