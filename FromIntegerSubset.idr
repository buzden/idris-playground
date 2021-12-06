import Data.Bits
import Data.DPair
import Data.Nat
import Data.So

namespace SubsetNat

  public export
  fromInteger : (x : Integer) ->
                {0 n : Nat} ->
                {auto 0 prf : fromInteger x `LT` n} ->
                Subset Nat (`LT` n)
  fromInteger x = Element (integerToNat x) prf

f : Int -> Int
f x = shiftR x 1
