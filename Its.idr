module Its

import Control.Monad.Maybe
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

data X a b = MkX a a b b

Show a => Show b => Show (X a b) where
  show (MkX a1 a2 b1 b2) = "MkX \{show a1} \{show a2} \{show b1} \{show b2}"

-- Iterator with external subiterators ---
itX : Applicative m => m a -> m b -> m (X a b)
itX ma mb = [| MkX ma ma mb mb |]

--- Running harness ---

xsc : (spending : List a) -> (cartesian : List b) -> List $ X a b
xsc as bs = fromMaybe [] $ runIdentity $ runMaybeT $ evalStateT as $ sequence $
              itX (pure cr) (pure <$> bs)
                @{Applicative.Compose} {m = List .: StateT _ . _ $ Identity}

--- Example run ---

theNats : List Nat
theNats = [100 .. 999]

theStrs : List String
theStrs = ["a", "b", "c"]

main : IO ()
main = for_ (xsc theNats theStrs) $ putStrLn . ("\n" ++) . show
