module Injective

%default total

interface Injective (ty : Type) (op : ty -> ty) where
  inj : (a : ty) -> (b : ty) -> op a = op b -> a = b
