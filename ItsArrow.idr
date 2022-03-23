module ItsArrow

import Data.Either -- due to non-public import in `Control.Arrow`

import Data.SortedSet

import Control.Arrow
import Control.Category

import Control.Monad.State

%default total

--- Utility ---

%inline
apW : Applicative m1 => Applicative m2 => Applicative m3 =>
      (a -> b -> c) -> (m1 $ m2 $ m3 a) -> (m1 $ m2 $ m3 b) -> m1 $ m2 $ m3 c
apW f x y = [| f x y |] where
  %inline pure : forall a. a -> m1 $ m2 $ m3 a
  pure = Prelude.pure @{Compose @{Compose}}
  %inline (<*>) : forall a, b. (m1 $ m2 $ m3 $ a -> b) -> (m1 $ m2 $ m3 a) -> m1 $ m2 $ m3 b
  (<*>) = Prelude.(<*>) @{Compose @{Compose}}

printAll : Foldable t => Show a => HasIO io => t a -> io Unit
printAll = traverse_ $ putStrLn . show

infixr 1 >>*>

-- Run the second arrow only for effects, discarding its result
(>>*>) : Arrow ar => ar a b -> ar b c -> ar a b
l >>*> r = l >>> (id &&& r) >>> arrow fst

-----------------------------------------
--- Generalised non-determinism arrow ---
-----------------------------------------

--- Datatype and its arrow instances ---

data NonDetS : Type -> Type -> Type -> Type where
  MkNonDetS : (a -> List $ State s $ List b) -> NonDetS s a b

Category (NonDetS s) where
  MkNonDetS l . MkNonDetS r = MkNonDetS $ r >=> \sb => pure $ join $ map (map join . sequence . join) $ map @{Compose} l sb
  id = MkNonDetS $ pure @{Compose @{Compose}}

Arrow (NonDetS s) where
  arrow f = MkNonDetS $ pure @{Compose @{Compose}} . f
  first  $ MkNonDetS f = MkNonDetS $ \(x, y) => map @{Compose @{Compose}} (, y) $ f x
  second $ MkNonDetS f = MkNonDetS $ \(x, y) => map @{Compose @{Compose}} (x, ) $ f y

  MkNonDetS f *** MkNonDetS g = MkNonDetS $ \(l, r) => apW (,) (f l) (g r)
  MkNonDetS f &&& MkNonDetS g = MkNonDetS $ \x => apW (,) (f x) (g x)

ArrowChoice (NonDetS s) where
  left $ MkNonDetS f = MkNonDetS $ \case
    Left  x => map @{Compose @{Compose}} Left $ f x
    Right x => pure @{Compose @{Compose}} $ Right x

ArrowZero (NonDetS s) where
  zeroArrow = MkNonDetS $ const neutral

ArrowPlus (NonDetS s) where
  MkNonDetS l <++> MkNonDetS r = MkNonDetS $ \x => l x <+> r x

--- Running the `NonDetS` arrow ---

run : s -> NonDetS s a b -> a -> List b
run s (MkNonDetS f) = join . evalState s . sequence . f

run' : s -> NonDetS s Unit b -> List b
run' s a = run s a ()

runDef : Monoid s => NonDetS s a b -> a -> List b
runDef = run neutral

vals : Monoid s => NonDetS s Unit a -> List a
vals = run' neutral

--- Connection between dynamic and static arrows ---

mkDynamic : (a -> NonDetS s Unit b) -> NonDetS s a b
mkDynamic f = MkNonDetS $ \x => let MkNonDetS g = f x in g ()

mkStatic : NonDetS s a b -> a -> NonDetS s Unit b
mkStatic (MkNonDetS f) x = MkNonDetS $ const $ f x

-- Identity properties

statDynId : (f : a -> NonDetS s Unit b) -> (x : a) -> mkStatic (mkDynamic f) x === f x
statDynId ff x with (ff x)
  _ | MkNonDetS gg with (gg ()) proof prf2
    _ | ggu = cong MkNonDetS $ rewrite sym prf2 in funext _ _ $ \() => Refl where
          funext : forall a, b. (f, g : a -> b) -> ((x : a) -> f x = g x) -> f = g

dynStatId : (ar : NonDetS s a b) -> mkDynamic (mkStatic ar) === ar
dynStatId $ MkNonDetS f = cong MkNonDetS Refl

--- Common particular iterators ---

namespace Static

  export
  nonDet : List a -> NonDetS s Unit a
  nonDet xs = MkNonDetS $ \() => pure @{Compose} <$> xs

  export
  resetSt : s -> NonDetS s Unit Unit
  resetSt x = MkNonDetS $ \() => pure $ state $ const (x, pure ())

namespace Dynamic

  export
  nonDet : NonDetS s (List a) a
  nonDet = MkNonDetS $ map $ pure @{Compose}

  export
  resetSt : NonDetS s s Unit
  resetSt = MkNonDetS $ \x => pure $ state $ const (x, pure ())

cr : NonDetS (List s) Unit s
cr = MkNonDetS $ \() => pure $ do
  x::xs <- get
    | [] => pure []
  put xs $> [x]

--- Wrapping into tupled state ---

joinSts : NonDetS s1 a b1 -> NonDetS s2 a b2 -> NonDetS (s1, s2) a (b1, b2)
joinSts (MkNonDetS f) (MkNonDetS g) = MkNonDetS $ \x => [| jo (f x) (g x) |] where
  jo : State s1 (List b1) -> State s2 (List b2) -> State (s1, s2) $ List (b1, b2)
  jo f' g' = state $ \(r1, r2) =>
    let (r1, bs1) = runState r1 $ f'
        (r2, bs2) = runState r2 $ g'
    in ((r1, r2), [| (bs1, bs2) |])

extStR : NonDetS s a b -> NonDetS (s, t) a b
extStR $ MkNonDetS f = MkNonDetS $ map (\f' => state $ \(s, t) => mapFst (, t) $ runState s f') . f

extStL : NonDetS s a b -> NonDetS (t, s) a b
extStL $ MkNonDetS f = MkNonDetS $ map (\f' => state $ \(t, s) => mapFst (t, ) $ runState s f') . f

prefix 9 ^*, *^

%inline
(^*) : NonDetS s a b -> NonDetS (t, s) a b
(^*) = extStL

(*^) : NonDetS s a b -> NonDetS (s, t) a b
(*^) = extStR

elimStR : NonDetS (s, t) a b -> s -> NonDetS t a b
elimStR (MkNonDetS f) initS = MkNonDetS $ map (\stST => state $ \t => mapFst snd $ runState (initS, t) stST) . f

elimStL : NonDetS (t, s) a b -> s -> NonDetS t a b
elimStL (MkNonDetS f) initS = MkNonDetS $ map (\stST => state $ \t => mapFst fst $ runState (t, initS) stST) . f

--- Monad state wrappers ---

wrapSt : (forall m. MonadState s m => a -> m b) -> NonDetS s a b
wrapSt f = MkNonDetS $ \x => pure $ f x <&> pure

modif : (a -> s -> s) -> NonDetS s a Unit
modif f = wrapSt $ modify . f

get : NonDetS s a s
get = wrapSt $ const get

--- Applicative syntax ---

Arrow ar => Functor (ar ll) where
  map f x = x >>> arrow f

Arrow ar => Applicative (ar ll) where
  pure = arrow . const
  l <*> r = (l &&& r) >>> arrow (uncurry id)

---------------------
--- Usage example ---
---------------------

--- Independent generation with spendings ---

-- Data structure --

data Y a b c = MkY a b c

data X a b c = MkX a a (Y a b ()) (Y a b c) c

Show a => Show b => Show c => Show (Y a b c) where
  show (MkY a b c) = "MkY \{show a} \{show b} \{show c}"

Show a => Show b => Show c => Show (X a b c) where
  show (MkX a1 a2 b1 b2 c) = "MkX \{show a1} \{show a2} (\{show b1}) (\{show b2}) \{show c}"

-- Iterator with external static subiterators ---

itY : Applicative m => m a -> m b -> m c -> m (Y a b c)
itY ma mb mc = [| MkY ma mb mc |]

-- If we prefer arrow combinators
itY' : Arrow ar => ar i a -> ar i b -> ar i c -> ar i (Y a b c)
itY' ara arb arc = (ara &&& arb &&& arc) >>> arrow (\(x, y, z) => MkY x y z)

itX : Applicative m => m a -> m b -> m c -> m (X a b c)
itX ma mb mc = [| MkX ma ma (itY ma mb [| () |]) (itY ma mb mc) mc |]

-- Running harness --

xsc : (spending1 : List a) -> (cartesian : List b) -> (spending2 : List c) -> List $ X a b c
xsc spending1 cartesian spending2 = run' (spending1, spending2) $ itX (*^ cr) (nonDet cartesian) (^* cr)

-- Example runs --

aLotOfNats : List Nat
aLotOfNats = [100 .. 999]

aFewNats : List Nat
aFewNats = [100 .. 130]

theStrs : List String
theStrs = ["a", "b", "c"]

theChrs : List Char
theChrs = chr <$> let k = ord 'a' in [k .. k + 25]

mainSp : IO ()
mainSp = for_ [aFewNats, aLotOfNats] $ \nats => do
  let xs = xsc nats theStrs theChrs
  for_ xs $ putStrLn . ("\n" ++) . show
  putStrLn "\n^^^^^^^^^"

--- Dependent generation ---

lists : NonDetS s Unit a -> NonDetS s Nat (List a)
lists (MkNonDetS ara) = MkNonDetS f where
  f : Nat -> List $ State s $ List $ List a
  f Z     = pure @{Compose @{Compose}} []
  f (S k) = apW (::) (ara ()) (f k)

depEx : NonDetS Unit Unit (List Char)
depEx = nonDet [0, 3, 4] >>> lists (nonDet ['a', 'b', 'c'])

mainDep : IO Unit
mainDep = printAll $ vals depEx

depExSp : NonDetS (List a) Unit (List a)
depExSp = nonDet [0, 3, 4] >>> lists cr

mainDepSp : IO Unit
mainDepSp = printAll $ run' [the Nat 100 .. 300] depExSp

--- Dependent generation with remembering ---

rememberGened : NonDetS s a b -> NonDetS (SortedSet b, s) a b
rememberGened super = ^* super >>*> *^ modif insert

gen1plusRem : NonDetS s inp a -> NonDetS (SortedSet a, s) inp (a, List a)
gen1plusRem genA = rememberGened genA &&& (pure 3 >>> lists (*^ get >>> arrow SortedSet.toList >>> nonDet))

mainDepRem : IO Unit
mainDepRem = printAll $ vals $ gen1plusRem {s=Unit} $ nonDet ['a', 'b', 'c', 'd']

mainDepRemSp : IO Unit
mainDepRemSp = printAll $ run' (empty, theChrs) $ nonDet [0, 1, 2] &&& gen1plusRem cr
