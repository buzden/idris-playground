module Injective

%default total

interface Injective (op : t -> t) where
  inj : (a : t) -> (b : t) -> op a = op b -> a = b

  inj' : {a : t} -> {b : t} -> op a = op b -> a = b
  inj' {a} {b} = inj a b

Injective S where
  inj = succInjective
