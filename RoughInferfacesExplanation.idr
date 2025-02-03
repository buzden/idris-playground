import Data.Vect

namespace Before

  interface X n a b where
    constructor MkX
    f : Vect n a -> b

namespace After

  data X : (n : Nat) -> (a : Type) -> (b : Type) -> Type where
    MkX : (f : Vect n a -> b) -> X n a b

  f : X n a b => Vect n a -> b
  f @{MkX f'} = f'

----

namespace Before

  X 5 a Nat where
    f _ = 5

  [NamedOne] X n a Bool where
    f _ = False

namespace After

  %hint
  X_5_a_Nat : X 5 a Nat
  X_5_a_Nat = MkX (\_ => 5)

  NamedOne : X n a Bool
  NamedOne = MkX (\_ => False)

----
----

namespace Before

  interface X n a b => Y n a b where
    constructor MkY
    g : b -> a

namespace After

  data Y : (n : Nat) -> (a : Type) -> (b : Type) -> Type where
    MkY : X n a b -> (g : b -> a) -> Y n a b

  g : Y n a b => b -> a
  g @{MkY _ g'} = g'

  %hint
  X_From_Y : Y n a b => X n a b
  X_From_Y @{MkY x _} = x

----

namespace Before

  Y 5 a Nat where
    g = ?foo

  Y n a Bool using Before.NamedOne where
    g = ?foo3

namespace After

  %hint
  Y_5_a_Nat : Y 5 a Nat
  Y_5_a_Nat = MkY %search ?foo2

  %hint
  Y_n_a_Bool : Y n a Bool
  Y_n_a_Bool = MkY NamedOne ?foo4
