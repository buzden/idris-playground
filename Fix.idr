%default total

public export
data Fix : (Type -> Type) -> Type where
  MkFix : Lazy (f $ Fix f) -> Fix f

public export
fix : f (Fix f) -> Fix f
fix = MkFix . delay

public export
unFix : Fix f -> f $ Fix f
unFix $ MkFix x = force x

export
covering
hylo : Functor f => (coalg : a -> f a) -> (alg : f b -> b) -> a -> b
hylo coalg alg x = alg $ coalg x <&> hylo coalg alg

export
covering
cataFix : Functor f => (alg : f a -> a) -> Fix f -> a
cataFix = hylo unFix

export
covering
anaFix : Functor f => (coalg : a -> f a) -> a -> Fix f
anaFix coalg = hylo coalg fix
