%foreign "scheme,chez:(lambda (a b f) (guard (x [#t '()]) (box (f 'check-constantness))))"
         "scheme,racket:(lambda (a b f) (with-handlers ([(lambda (x) #t) (lambda (e) '())]) (box (f 'check-constantness))))"
checkIfConst : (f : a -> b) -> Maybe b

const5 : Nat -> Nat
const5 x = 5

inc : Nat -> Nat
inc x = x + 1

trueOr : Bool -> Bool
trueOr b = True || b

pureList : Nat -> List Nat
pureList = pure

natId : Nat -> Nat
natId = id

main : IO ()
main = do
  putStr "const5\n  "
  printLn $ checkIfConst const5
  putStr "inc\n  "
  printLn $ checkIfConst inc
  putStr "trueOr\n  "
  printLn $ checkIfConst trueOr
  putStr "pureList\n  "
  printLn $ checkIfConst pureList
  putStr "natId\n  "
  printLn $ checkIfConst natId
