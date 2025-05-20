import public Data.So

%default total

public export
NotTuple : Type -> Bool
NotTuple (_, _) = False
NotTuple _      = True

public export
data HasNthTuple : (idx : Nat) -> (tup : Type) -> Type -> Type where
  [search idx tup]
  Only  : So (NotTuple t) => HasNthTuple Z t t
  Here  : HasNthTuple Z (t, a) t
  There : HasNthTuple n x t -> HasNthTuple (S n) (a, x) t

export
projTuple : (n : Nat) -> HasNthTuple n a t => a -> t
projTuple 0     @{Only}    x      = x
projTuple 0     @{Here}    (x, _) = x
projTuple (S k) @{There h} (_, y) = projTuple k y

x0of3 : (Nat, String, Double) -> ?
x0of3 = projTuple 0

x1of3 : (Nat, String, Double) -> String
x1of3 = projTuple 1

x2of3 : (Nat, String, Double) -> Double
x2of3 = projTuple 2
