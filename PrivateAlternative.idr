module PrivateAlternative

import Language.Reflection

%language ElabReflection

namespace Inner

  private
  f1 : Nat
  f1 = 4

  export
  f2 : Nat -> Nat
  f2 = (+5)

  public export
  f3 : Nat -> Nat -> Nat
  f3 = (*)

  export %macro %inline
  f : Elab a
  f = check $ IAlternative EmptyFC FirstSuccess
    [ `(f1)
    , `(f2)
    , `(f3)
    ]

  y1 : Nat
  y1 = f

  y2 : Nat -> Nat
  y2 = f

failing
  x1 : Nat
  x1 = f

x2 : Nat -> Nat
x2 = f
