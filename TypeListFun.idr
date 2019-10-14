module TypeListToFunction

%default total

TypeListFun : List Type -> Type
TypeListFun [] = Unit
TypeListFun (x::xs) = x -> TypeListFun xs

typeListFun : (ts : List Type) -> TypeListFun ts
typeListFun [] = ()
typeListFun (_::xs) = \_ => typeListFun xs
