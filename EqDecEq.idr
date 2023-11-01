import Data.So

%default total

interface Eq a => EqIsDecEq a where
  eqIsDecEq : (x, y : a) -> So (x == y) -> x = y

EqIsDecEq Nat where
  eqIsDecEq 0     0     _ = Refl
  eqIsDecEq (S k) (S j) _ with (k == j) proof kj
    _ | True with (eqIsDecEq k j $ eqToSo kj)
      _ | xx = cong S xx

EqIsDecEq a => EqIsDecEq (List a) where
  eqIsDecEq []      []      _ = Refl
  eqIsDecEq (x::xs) (y::ys) _ with (x == y) proof xy
    _ | True with (xs == ys) proof xsys
      _ | True = do
        rewrite eqIsDecEq x y $ eqToSo xy
        rewrite eqIsDecEq xs ys $ eqToSo xsys
        Refl

---

%hint
useEqIsDecEq : EqIsDecEq a => {x, y : a} -> So (x == y) => x = y
useEqIsDecEq @{_} @{s} = eqIsDecEq x y s

f : (a, b : Nat) -> ()
f a b with (decSo $ a == b)
  _ | Yes ab = let ab = the (a = b) %search in ?foo_ues
  _ | No nab = ?foo_no
