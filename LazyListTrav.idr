module LazyListTrav

import Data.List.Lazy

import Debug.Trace

%default total

public export
Traversable LazyList where
  traverse = map force .: tr where
    tr : (a -> f b) -> LazyList a -> f (Lazy (LazyList b))
    tr g [] = pure []
    tr g (x::xs) = [| g x :: tr g xs |] where
      (::) : forall a. a -> Lazy (LazyList a) -> Lazy (LazyList a)
      (::) x xs = delay $ Lazy.(::) x xs

debugList : Nat -> LazyList Nat
debugList n = iterateN n f 1 where
  f : Nat -> Nat
  f x = trace "arg: \{show x}" $ x + 1

d : Applicative f => f $ LazyList Nat
d = map (Lazy.take 3) $ traverse pure $ debugList 500
