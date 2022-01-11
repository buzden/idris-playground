module IndentedClosingBracket

{
  import Data.Fin
}

{

namespace A' { x : Nat; x = 4 }

namespace A {
x : Nat
x = 4
  }

namespace B {
x : Nat
x = 5
  }

export
x : Nat
x = let {
    a = 4 {| x => 54
          }
  } in 4

interface X where {
  xxx : Nat
    }

mm : Monad m => m Nat
mm = do {
  pure 4
}

f : Nat
f = x where {
    xx : Nat
    xx = 3
      }

%hide Nat

public export
Prelude.Nat : Type
Prelude.Nat = Integer

y : Nat
y = 3

g : Bool
g = case y of
      help => ?foo

  }
