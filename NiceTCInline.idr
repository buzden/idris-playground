%default total

%tcinline
stop : List Bool -> Nat
stop [] = 0
stop (False :: xs) = stop xs
stop (True :: xs) = 1 + stop (False :: xs)
