f : {0 m : Type -> Type} -> a = b -> m a -> m b
f eq ma = do
  rewrite sym eq
  ma
