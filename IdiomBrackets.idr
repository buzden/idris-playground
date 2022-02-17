-- Experimental demo that idiom brackets do not need `<$>`, only `pure` and `<*>`

data X a = MkX

pure : a -> X a
pure _ = MkX

(<*>) : X (a -> b) -> X a -> X b
(<*>) _ _ = MkX

zero : Nat -> X Nat
zero x = [| x |]

one : X Nat -> X Nat
one x = [| (+1) x |]

two : X Nat -> X Nat -> X (Nat, Nat)
two x y = [| (,) x y |]
