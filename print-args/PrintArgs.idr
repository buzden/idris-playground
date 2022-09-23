module PrintArgs

import System

%default total

main : IO ()
main = do
  args <- getArgs
  for_ args $ \arg =>
    putStrLn "'\{arg}'"
