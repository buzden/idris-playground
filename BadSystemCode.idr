module BadSystemCode

import System

main : IO ()
main = system "some-non-existent-command" >>= putStrLn . show -- should print `-1`
