-- This is for the answer to the question in the telegram chat: https://t.me/c/1062361327/47825

data IsSingleton : Bool -> Type where
  One  : Nat -> IsSingleton True
  Many : List Nat -> IsSingleton False

Nil : IsSingleton False
Nil = Many []

(::) : Nat -> IsSingleton False -> IsSingleton False
(::) x (Many xs) = Many $ x :: xs

fromInteger : (n : Integer) -> IsSingleton True
fromInteger = One . fromInteger

mkSingle : (x : Bool) -> IsSingleton x
mkSingle True = 0
mkSingle False = [1, 2]
