Y : Type
X : Type
Term : Type -> Type

erase : Term a -> Y

unc : (x : Term a) -> erase x = y -> (x : Term a ** erase x = y)
unc x p = (x ** p)

f : (x : Term a) -> erase x = y -> X = a -> (x' : Term X ** erase x' = y)
f x h p = rewrite p in unc x h
