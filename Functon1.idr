1 f : (1 _ : Nat) -> Nat
f x = S x -- + 1 -- !! Wow, `+` is not linear! I can't use it here!

g : Nat -> Nat
g x = f x

h : Nat -> Nat
h x = let fx = f x in ?foo -- fx is linear because the whole function is!

--- Passing the functions ---

-- Like `f` but without `1` quantity on the whole function.
f' : (1 _ : Nat) -> Nat
f' x = S x

fi : (1 f : (1 _ : Nat) -> Nat) -> Nat -> Nat
fi f x = let fx = f x in fx -- ?foo_fi -- fx is linear like above

fi_f : Nat -> Nat
fi_f = fi f

fi_f' : Nat -> Nat
fi_f' = fi f'

fj : (f : (1 _ : Nat) -> Nat) -> Nat -> Nat
fj f x = let fx = f x in ?foo_fj -- fx is NOT linear

fj_f' : Nat -> Nat
fj_f' = fj f'

useTwice : Nat -> Nat -> Nat
useTwice x y = let fx = f x
                   fy = f y
                   xx = f
               in ?foo_twice

fj_f : Nat -> Nat
fj_f = fj ?foo_f -- if we try `f` here, we get "trying to use f in non-linear context"

------

local : Nat -> Nat
local x = let 1 foj : (1 _ : Nat) -> Nat
              foj x = S x in
          let 1 foy : (1 _ : Nat) -> Nat
              foy = foj in
          --let 1 fox = foj in
          x
  where
    1 foo : (1 _ : Nat) -> Nat
    foo x = S x
