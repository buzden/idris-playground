isList : (ty : Type) -> Bool
isList $ List _ = True
isList _        = False

toListType : Type -> Type
toListType t = if isList t then t else List t

toList : (t : Type) -> (v : t) -> toListType t
toList t v with (isList t)
  toList t v | True  = v
  toList t v | False = [v]
