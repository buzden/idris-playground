import Data.String

x : Char
x = '\BEL'
x = '\\'
x = '\''
x = '\o755'
x = '\^'
x = '\10'

s : String
s = "ab \o755 ^A@_"

xx : Int
xx = 0o7_5_5

main : IO ()
main = putStrLn $ singleton x
