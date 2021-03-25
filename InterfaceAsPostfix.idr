interface (.defaultable) a where
  defa : a

(.defaultable) Int where
  defa = 0

f : Num a => a.defaultable => a -> a
f x = x + defa
