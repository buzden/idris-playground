module TypeListToFunction

TypeListFun : List Type -> Type
TypeListFun [] = Unit
TypeListFun (x::xs) = x -> TypeListFun xs
