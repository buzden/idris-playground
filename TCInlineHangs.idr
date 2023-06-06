%default total

%tcinline
incAll : Stream Nat -> Stream Nat
incAll (x::xs) = S x :: incAll xs

--%tcinline
incAll' : Stream Nat -> Stream Nat
incAll' = \(x::xs) => S x :: incAll' xs

--%tcinline
zs : Stream Nat -> Stream Nat
zs xs = Z :: zs xs

--%tcinline
zs' : Stream Nat
zs' = Z :: zs'
