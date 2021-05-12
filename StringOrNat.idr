import Data.So

fromString : String -> Either String Nat
fromString = Left

fromInteger : (x : Integer) -> (0 _ : So (x >= 0)) => Either String Nat
fromInteger x = Right $ integerToNat x

x : List $ Either String Nat
x = ["x", 1, 2, "y"]
