import Decidable.Equality

data Y : Nat -> Nat -> Type where
  A : Y (S n) (S n)

ff1 : (n, k : Nat) -> Maybe $ Y n k
ff1 (S n) (S k) = case decEq k n of
                   No _ => empty
                   Yes p => rewrite p in ?ff1_rhs_1
ff1 (S n) (S k) = case decEq n k of
                   No _ => empty
                   Yes p => rewrite p in ?ff1_rhs_2
ff1 n k = case decEq k n of
                   No _ => empty
                   Yes p => rewrite p in ?ff1_rhs_3
ff1 n k = case decEq n k of
                   No _ => empty
                   Yes p => rewrite p in ?ff1_rhs_4

ff2 : (n, k : Nat) -> Maybe $ Y n k
ff2 (S n) (S k) = case decEq k n of
                   No _ => empty
                   Yes Refl => ?ff2_rhs_1
ff2 (S n) (S k) = case decEq n k of
                   No _ => empty
                   Yes Refl => ?ff2_rhs_2
ff2 n k = case decEq k n of
                   No _ => empty
                   Yes Refl => ?ff2_rhs_3
ff2 n k = case decEq n k of
                   No _ => empty
                   Yes Refl => ?ff2_rhs_4
