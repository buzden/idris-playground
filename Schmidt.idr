-- An answer to a question by Nicolas Alexander Schmidt in the idris mailing list.

interface Foo (p : Type -> Type) where
  bar : {a : _} -> p a => a

data OnlyInt : Type -> Type where
  NiceCase : OnlyInt Int
  BadCase  : Void -> OnlyInt x

Foo OnlyInt where
  bar {a=Int} @{NiceCase}  = 0
  bar {a=x}   @{BadCase y} = absurd y
