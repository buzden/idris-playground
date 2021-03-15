import Data.Fuel

%default covering -- total

interface X a where
  ls : Fuel -> List a

mutual

  X Nat where
    ls Dry      = []
    ls (More f) = [length $ the (List Bool) $ ls f]

  X Bool where
    ls Dry      = []
    ls (More f) = [null $ the (List Nat) $ ls f]

main : IO Unit
main =
  putStrLn $ show $ the (List Nat) $ ls $ limit 6
