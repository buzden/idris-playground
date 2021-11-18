ts1 : Applicative m => m a -> m b -> m (a, a, b)
ts1 as bs = [| (,,) as as bs |]

ts2 : Applicative m => m a -> m b -> m (a, a, b)
ts2 as bs = [| (as, as, bs) |]
