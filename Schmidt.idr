-- An answer to a question by Nicolas Alexander Schmidt in the idris mailing list.

%default total

interface Foo (p : Type -> Type) where
  bar : {0 a : _} -> p a => a

data OnlyInt : Type -> Type where
  NiceCase : OnlyInt Int

Foo OnlyInt where
  bar @{NiceCase} = 0

-- Why can't we remove `BadCase` and its match from `bar` implementation?
-- Compiler claims that match in not exhaustive, however, everything works for `Nat`s:

data X : Nat -> Type where
  X10 : X 10

bbar : {a : _} -> X a -> Int
bbar {a=10} X10 = 1
