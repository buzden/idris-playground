import Data.Nat

ltTransitive : (n, m, k : Nat) -> n `LT` m -> m `LT` k -> n `LT` k

ltAntiSymmetric : (n, m : Nat) -> (n `LT` m) -> Not (m `LT` n)
ltAntiSymmetric n m nm mn = do
  let u = ltTransitive n m n nm mn
  case u of
    LTEZero impossible

ltAntiSymmetric'' : (n, m : Nat) -> (n `LT` m) -> Not (m `LT` n)
ltAntiSymmetric'' n m nm mn = do
  case ltTransitive n m n nm mn of
    LTEZero impossible

ltAntiSymmetric' : (n, m : Nat) -> (n `LT` m) -> Not (m `LT` n)
ltAntiSymmetric' n m nm mn = do
  let u = ltTransitive n m n nm mn
  case u of
    LTEZero impossible
    LTESucc _ impossible
