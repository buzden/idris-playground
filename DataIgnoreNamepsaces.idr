namespace X

  record Y where
    constructor MkY
    field1 : Nat

  data Z : Type where
    MkZ : Nat -> Z

namespace Y
  g : Y
  h : Z
