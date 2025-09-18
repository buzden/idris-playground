%default total

interface I a where
  foo : a

I Unit where
  foo = MkUnit

--I Builtin.Unit where
--  foo = MkUnit

namespace X
  export
  T : Type
  T = Unit

  export
  I T where
    foo = MkUnit

  failing "Multiple solutions"
    x' = foo {a=Unit}

x = foo {a=Unit}
