module QuantityInDataDef

import Data.List

-- based on the datatype from Brady's lectures

data RunLength : (0 _ : List ty) -> Type where
  Empty : RunLength []
  Run : (n : Nat) -> (x : ty) -> RunLength more -> RunLength (replicate n x ++ more)
  Ruin : (x : List ty) -> RunLength x -- I wish I had a way to disallow this J_J
