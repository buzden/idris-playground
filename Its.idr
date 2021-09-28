module Its

import Control.Monad.State

import Data.Maybe

%default total

--- Staty iterator ---

cr : Alternative m => MonadState (List a) m => m a
cr = do
  (x::xs) <- get
    | [] => empty
  put xs $> x

--- Data structure ---

data Y a b = MkY a b

data X a b = MkX a a (Y a b) (Y a b)

Show a => Show b => Show (Y a b) where
  show (MkY a b) = "MkY \{show a} \{show b}"

Show a => Show b => Show (X a b) where
  show (MkX a1 a2 b1 b2) = "MkX \{show a1} \{show a2} (\{show b1}) (\{show b2})"

-- Iterator with external subiterators ---

itY : Applicative m => m a -> m b -> m (Y a b)
itY ma mb = [| MkY ma mb |]

itX : Applicative m => m a -> m b -> m (X a b)
itX ma mb = [| MkX ma ma (itY ma mb) (itY ma mb) |]

--- Special data for special needs (tracking) ---

data TrackFull a = MkTrackFull (Maybe (a, Bool))

Functor TrackFull where
  map f (MkTrackFull m) = MkTrackFull $ mapFst f <$> m

Applicative TrackFull where
  pure = MkTrackFull . pure . (,True)
  MkTrackFull f <*> MkTrackFull x = MkTrackFull $ (\(f, bl) => bimap f (bl &&)) <$> f <*> x

Alternative TrackFull where
  empty = MkTrackFull empty
  x@(MkTrackFull (Just _)) <|> _             = x
  MkTrackFull Nothing      <|> MkTrackFull y = MkTrackFull $ y <&> mapSnd (const False)

Monad TrackFull where
  MkTrackFull m >>= f = MkTrackFull $ m >>= \(a, bl) => let MkTrackFull n = f a in mapSnd (bl &&) <$> n

-- like `fromMaybe` but for `TrackFull`
fromTrackEnd : Lazy a -> TrackFull a -> (a, Bool)
fromTrackEnd x (MkTrackFull cont) = fromMaybe (x, False) cont

--- Running harness ---

-- Like specialised `sequence` but produces the longest possible non-failing sequence
-- using recovering with `Alternative`
runPartialCartesian : Monad m => Alternative m => List (StateT s m a) -> StateT s m (List a)
runPartialCartesian []           = pure []
runPartialCartesian (curr::rest) = ST $ \s => do
  (s, l) <- map pure <$> runStateT s curr          <|> pure (s, [])
  (s, r) <- runStateT s (runPartialCartesian rest) <|> pure (s, [])
  pure (s, l ++ r)

xsc : (spending : List a) -> (cartesian : List b) -> (List $ X a b, Bool)
xsc as bs = fromTrackEnd [] $ evalStateT as $ runPartialCartesian $
              itX (pure cr) (pure <$> bs) @{Applicative.Compose}

--- Example run ---

aLotOfNats : List Nat
aLotOfNats = [100 .. 999]

aFewNats : List Nat
aFewNats = [100 .. 130]

theStrs : List String
theStrs = ["a", "b", "c"]

main : IO ()
main = for_ [aFewNats, aLotOfNats] $ \nats => do
  let (xs, full) = xsc nats theStrs
  for_ xs $ putStrLn . ("\n" ++) . show
  putStrLn "\n^^^^^^^^^ cartesian iteration was\{if full then "" else "n't"} full"
