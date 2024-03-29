failing "Mismatch between: a and a"
  f : {a : Type} -> List a
  f = g where
    g : {a : Type} -> List a
    g = Nil {a}

namespace ExplicitBind

  f : {a : Type} -> List a
  f = g where
    g : {a : Type} -> List a
    g {a} = Nil {a}

failing "Mismatch between: a and b"
  f : (ty : Type) -> (tyList : List ty) => List ty
  f a = g a where
    g : (ty : Type) -> (tyList : List ty) => List ty
    g b = do
      x <- tyList
      pure x

namespace ExplicitBind'

  f : (ty : Type) -> List ty => List ty
  f a @{tyList} = g a where
    g : (ty : Type) -> List ty => List ty
    g b @{tyList} = do
      x <- tyList
      pure x

