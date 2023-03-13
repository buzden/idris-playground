infixl 0 .|

public export %inline %tcinline
(.|) : a -> a
(.|) = id

f : Maybe .| List Nat -> Maybe .| List Nat
f $ Just (x::xs) = Just xs
f _              = Nothing

