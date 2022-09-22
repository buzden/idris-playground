%default total

public export
data Fix : (Type -> Type) -> Type where
  MkFix : Lazy (f $ Fix f) -> Fix f
