module Its

import Control.Monad.State
import Control.Monad.Writer

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

--- Cycling ---

namespace Cycling

  --- Cycling any stateful monad using `Alternative` recovering ---

  covering
  cycleReloaded : Alternative m => MonadState s m => s -> m a -> m a
  cycleReloaded s act = act <|> put s *> cycleReloaded s act

  --- Special monad for tracking Alternative's `empty` per value ---

  -- Boolean flag means "all were `empty`"
  data TrackPer : (Type -> Type) -> Type -> Type where
    MkTrackPer : StateT Bool m a -> TrackPer m a

  unTrackPer : TrackPer m a -> StateT Bool m a
  unTrackPer $ MkTrackPer x = x

  Monad m => Functor (TrackPer m) where
    map f (MkTrackPer m) = MkTrackPer $ f <$> m

  Monad m => Applicative (TrackPer m) where
    pure = MkTrackPer . pure
    MkTrackPer f <*> MkTrackPer x = MkTrackPer $ f <*> x

  Alternative m => Monad m => Alternative (TrackPer m) where
    empty = MkTrackPer empty
    MkTrackPer l <|> r = MkTrackPer $ l <|> put True *> unTrackPer r

  Monad m => Monad (TrackPer m) where
    MkTrackPer m >>= f = MkTrackPer $ m >>= unTrackPer . f

--  runTrackPer : Functor m => TrackPer m a -> m (a, Bool)
--  runTrackPer = map (\(a, b) => (b, a)) . runStateT False . unTrackPer

  --- Running harness ---

  -- failfast like `sequence`, unlike `runCartesianPartial`
  runPerTracked : Monad m => List (StateT s (TrackPer m) a) -> StateT s m $ List (a, Bool)
  runPerTracked = runPerTracked' False where
    runPerTracked' : (trackPerState : Bool) -> List (StateT s (TrackPer m) a) -> StateT s m $ List (a, Bool)
    runPerTracked' _  []      = pure []
    runPerTracked' tr (x::xs) = ST $ \s => do
      (tr, s, a) <- runStateT tr $ unTrackPer $ runStateT s x
      (map . map) ((a, tr)::) $ runStateT s $ runPerTracked' tr xs

  covering
  xcsc : (spending : List a) -> (cartesian : List b) -> List $ (X a b, Bool)
  xcsc as bs = fromMaybe [] $ evalStateT as $ runPerTracked $
                 itX (pure $ cycleReloaded as cr) (pure <$> bs) @{Applicative.Compose}

  --- Example run ---

  export covering
  mainCyc : IO ()
  mainCyc = for_ [aFewNats, aLotOfNats] $ \nats => do
    let xs = xcsc nats theStrs
    for_ xs $ putStrLn . ("\n" ++) . show
    putStrLn "\n^^^^^^^^^"
