1 f : (1 _ : Nat) -> Nat
f x = S x -- + 1 -- !! Wow, `+` is not linear! I can't use it here!

g : Nat -> Nat
g x = f x

h : Nat -> Nat
h x = let fx = f x in ?foo -- fx is linear because the whole function is!
