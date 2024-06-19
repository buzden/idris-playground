%default total

f : (x : Nat) -> {default (S x) n : Nat} -> Nat
f x = x + n

U : Nat
U = f 5

u_corr : U = 11
u_corr = Refl
