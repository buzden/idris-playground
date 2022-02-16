module ItsArrow

import Data.Either -- due to non-public import in `Control.Arrow`

import Control.Arrow
import Control.Category

import Control.Monad.State

%default total

-----------------------------------------
--- Generalised non-determinism arrow ---
-----------------------------------------

data NonDetS : Type -> Type -> Type -> Type where
  MkNonDetS : (a -> State s $ List b) -> NonDetS s a b

Category (NonDetS s) where
  MkNonDetS l . MkNonDetS r = MkNonDetS $ (>=>) r l @{Compose}
  id = MkNonDetS $ pure @{Compose}

Arrow (NonDetS s) where
  arrow f = MkNonDetS $ pure @{Compose} . f
  first  $ MkNonDetS f = MkNonDetS $ \(x, y) => map @{Compose} (, y) $ f x
  second $ MkNonDetS f = MkNonDetS $ \(x, y) => map @{Compose} (x, ) $ f y

ArrowChoice (NonDetS s) where
  left $ MkNonDetS f = MkNonDetS $ \case
    Left  x => map @{Compose} Left $ f x
    Right x => pure @{Compose} $ Right x

ArrowZero (NonDetS s) where
  zeroArrow = MkNonDetS $ const $ pure neutral

ArrowPlus (NonDetS s) where
  MkNonDetS l <++> MkNonDetS r = MkNonDetS $ \x => [| l x <+> r x |]

run : s -> NonDetS s a b -> a -> List b
run s (MkNonDetS f) = evalState s . f

run' : s -> NonDetS s Unit b -> List b
run' s a = run s a ()

runDef : Monoid s => NonDetS s a b -> a -> List b
runDef = run neutral

vals : Monoid s => NonDetS s Unit a -> List a
vals = run' neutral

namespace Static

  export
  nonDet : List a -> NonDetS s Unit a
  nonDet xs = MkNonDetS $ \() => pure xs

  export
  resetSt : s -> NonDetS s Unit Unit
  resetSt x = MkNonDetS $ \() => state $ const $ (x, pure ())

namespace Dynamic

  export
  nonDet : NonDetS s (List a) a
  nonDet = MkNonDetS pure

  export
  resetSt : NonDetS s s Unit
  resetSt = MkNonDetS $ \x => state $ const $ (x, pure ())

cr : NonDetS (List s) Unit s
cr = MkNonDetS $ \() => do
  x::xs <- get
    | [] => pure []
  put xs $> [x]

joinSts : NonDetS s1 a b1 -> NonDetS s2 a b2 -> NonDetS (s1, s2) a (b1, b2)
joinSts (MkNonDetS f) (MkNonDetS g) = MkNonDetS $ \x => state $ \(r1, r2) =>
  let (r1, bs1) = runState r1 $ f x
      (r2, bs2) = runState r2 $ g x
  in ((r1, r2), [| (bs1, bs2) |])

extStR : NonDetS s a b -> NonDetS (s, t) a b
extStR $ MkNonDetS f = MkNonDetS $ \x => state $ \(s, t) => mapFst (, t) $ runState s $ f x

extStL : NonDetS s a b -> NonDetS (t, s) a b
extStL $ MkNonDetS f = MkNonDetS $ \x => state $ \(t, s) => mapFst (t, ) $ runState s $ f x

--- Syntax ---

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

itY : Arrow ar => ar xx a -> ar xx b -> ar xx c -> ar xx (Y a b c)
itY ma mb mc = [| MkY ma mb mc |]

itX : Arrow ar => ar xx a -> ar xx b -> ar xx c -> ar xx (X a b c)
itX ma mb mc = [| MkX ma ma (itY ma mb [| () |]) (itY ma mb mc) mc |]

-- Running harness --

xsc : (spending1 : List a) -> (cartesian : List b) -> (spending2 : List c) -> List $ X a b c
xsc spending1 cartesian spending2 = run' (spending1, spending2) $ itX (extStR cr) (nonDet cartesian) (extStL cr)

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
  f : Nat -> State s $ List $ List a
  f Z     = pure [ [] ]
  f (S k) = do
    heads <- ara ()
    tails <- f k
    pure [| heads :: tails |]

depEx : NonDetS Unit Unit (List Char)
depEx = nonDet [0, 3, 4] >>> lists (nonDet ['a', 'b', 'c'])

mainDep : IO Unit
mainDep = traverse_ (putStrLn . show) $ vals depEx

depExSp : NonDetS (List a) Unit (List a)
depExSp = nonDet [0, 3, 4] >>> lists cr

mainDepSp : IO Unit
mainDepSp = traverse_ (putStrLn . show) $ run' [the Nat 100 .. 300] depExSp
