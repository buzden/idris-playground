module IncoherentIDefAndPatClauseNames

import Language.Reflection

%language ElabReflection

declBody : Elab ()
declBody = declare [
    IDef EmptyFC `{test} [
      PatClause EmptyFC
        (IVar EmptyFC `{test2})
        (IPrimVal EmptyFC $ BI 4)
    ]
  ]

test : Integer
test2 : Integer

%runElab declBody
