h : Monad m => Int -> m (Maybe Int)

f : Int -> Maybe Int

g : Monad m => m Int
g = do
  Just y <- h 5
    | Nothing => pure 0
  let Just x = f 4
    | Nothing => pure 4
  pure $ x + y
