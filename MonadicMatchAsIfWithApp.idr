a : Monad m => (Unit -> Unit) -> m $ Maybe ()

f : Monad m => m ()
f = do
  Just _ <- a id
    | Nothing => pure ()

  Just _ <- a id
  | Nothing => pure ()

  Just _ <- a $ \() => ()
  | Nothing => pure ()

  Just _ <- a $ \() => ()
    | Nothing => pure ()

  pure ()
