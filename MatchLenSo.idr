import Data.Nat
import Data.So

%default total

record X where
  constructor MkX
  field1 : Nat; field2 : String

f : (xs : List String) -> So (length xs >= 2) => String
f $ first :: second :: rest = first

g : (xs : List String) -> length xs `GTE` 2 => String
g $ first :: rest = first
