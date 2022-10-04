import Data.Buffer

%default total

doubleFromBits64 : HasIO io => Bits64 -> io Double
doubleFromBits64 n = do
  Just bf <- newBuffer 8
    | Nothing => pure $ 0.0/0
  setBits64 bf 0 n
  getDouble bf 0
