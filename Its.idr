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

--- `MonadState` for `StateT` on pairs ---

export
Monad m => MonadState l (StateT (l, r) m) where
  get = Builtin.fst <$> get
  put = modify . mapFst . const

export
Monad m => MonadState r (StateT (l, r) m) where
  get = Builtin.snd <$> get
  put = modify . mapSnd . const

--- Data structure ---

data Y a b c = MkY a b c

data X a b c = MkX a a (Y a b ()) (Y a b c) c

Show a => Show b => Show c => Show (Y a b c) where
  show (MkY a b c) = "MkY \{show a} \{show b} \{show c}"

Show a => Show b => Show c => Show (X a b c) where
  show (MkX a1 a2 b1 b2 c) = "MkX \{show a1} \{show a2} (\{show b1}) (\{show b2}) \{show c}"

-- Iterator with external subiterators ---

itY : Applicative m => m a -> m b -> m c -> m (Y a b c)
itY ma mb mc = [| MkY ma mb mc |]

itX : Applicative m => m a -> m b -> m c -> m (X a b c)
itX ma mb mc = [| MkX ma ma (itY ma mb [| () |]) (itY ma mb mc) mc |]

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

xsc : (spending1 : List a) -> (cartesian : List b) -> (spending2 : List c) -> (List $ X a b c, Bool)
xsc as bs cs = fromTrackEnd [] $ evalStateT (as, cs) $ runPartialCartesian $
              itX (pure cr) (pure <$> bs) (pure cr) @{Applicative.Compose}

--- Example run ---

aLotOfNats : List Nat
aLotOfNats = [100 .. 999]

aFewNats : List Nat
aFewNats = [100 .. 130]

theStrs : List String
theStrs = ["a", "b", "c"]

theChrs : List Char
theChrs = chr <$> let k = ord 'a' in [k .. k + 25]

main : IO ()
main = for_ [aFewNats, aLotOfNats] $ \nats => do
  let (xs, full) = xsc nats theStrs theChrs
  for_ xs $ putStrLn . ("\n" ++) . show
  putStrLn "\n^^^^^^^^^ cartesian iteration was\{the String $ if full then "" else "n't"} full"
