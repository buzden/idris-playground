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

--- Running harness ---

-- Like `sequence` but produces the longest possible non-failing sequence
runPartialCartesian : List (StateT s Maybe a) -> StateT s Maybe (List a)
runPartialCartesian [] = pure []
runPartialCartesian (curr::rest) = ST $ \s => do
  let Just (s, a) = runStateT s curr
    | Nothing => runStateT s $ runPartialCartesian rest -- or just `Nothing` for fail-fast semantics
  let Just (s, as) = runStateT s $ runPartialCartesian rest
    | Nothing => Just (s, [a])
  Just (s, a::as)

xsc : (spending : List a) -> (cartesian : List b) -> List $ X a b
xsc as bs = fromMaybe [] $ evalStateT as $ runPartialCartesian $
              itX (pure cr) (pure <$> bs) @{Applicative.Compose}

--- Example run ---

theNats : List Nat
theNats = [100 .. 110] -- 999]

theStrs : List String
theStrs = ["a", "b", "c"]

main : IO ()
main = for_ (xsc theNats theStrs) $ putStrLn . ("\n" ++) . show
