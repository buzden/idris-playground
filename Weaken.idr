module Weaken

import Data.Fin

weaken1 : (fn : Fin n) -> (fsn : Fin (S n) ** finToNat fn = finToNat fsn)
weaken1 FZ = (FZ ** Refl)
weaken1 (FS n) with (weaken1 n)
  | (nw ** nat_n_eq_nat_nw) = (FS nw ** eqSucc (finToNat n) (finToNat nw) nat_n_eq_nat_nw)
