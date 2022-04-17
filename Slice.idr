-- Born in discussions with Alexey Demakov while his learning of dependent types --

import Data.Nat
import Data.Vect

--data Slice : Nat -> Type where
--  MkSlice : Nat -> (length : Nat) -> Slice length

--(.offset) : Slice l -> Nat
--(.offset) $ MkSlice o _ = o

record Slice (0 length : Nat) where
  constructor MkSlice
  offset : Nat
  length : Nat

-- Look, `record` syntax may produce non-trivial GADT!
-- Once you match `MkSlice`, `l` from type is unified with `length`:

slice : (s : Slice l) -> Vect (s.offset + l + n) a -> Vect l a
slice $ MkSlice offset length =
  rewrite sym $ plusAssociative offset length n in
  take length . drop offset
