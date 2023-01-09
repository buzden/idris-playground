interface X where
  x : Nat

f : X => Nat
f = x + 1

namespace NoHintArg

  %defaulthint
  DefaultX : X
  DefaultX = D where
    [D] X where x = 5

  fDef : Nat
  fDef = f

namespace WithHintArg

  interface Y' where
    y : Nat

  Y' where
    y = 6

  %defaulthint
  DefaultX : Y' => X
  DefaultX = D where
    [D] X where x = 5

  fDef : Nat
  fDef = f
