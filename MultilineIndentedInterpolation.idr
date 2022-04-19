import Data.String

main : IO Unit
main = putStrLn """
  int main() {
    \{unlines ["int x = 0;", "return 0;"]}
  }
  """
