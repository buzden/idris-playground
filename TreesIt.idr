module TreesIt

import Control.Monad.Reader
import Control.Monad.State

import Data.List

record LeftToIterate a where
  constructor MkLeftToIterate
  leftToIterate : List a

record OriginalValues a where
  constructor MkOriginalValues
  originalValues : List a

nothingLeft : LeftToIterate a
nothingLeft = MkLeftToIterate empty

origToLeft : OriginalValues a -> LeftToIterate a
origToLeft = MkLeftToIterate . originalValues

%inline
Iterable'' : Type -> (Type -> Type) -> Type
Iterable'' a m = (MonadState (LeftToIterate a) m, MonadReader (OriginalValues a) m)

next'' : Iterable'' a m => m a
next'' = do
  gg <- get
  case leftToIterate gg of
    []      => asks origToLeft >>= put >> next''
    (x::xs) => put (MkLeftToIterate xs) $> x

%inline
ItT : Type -> (Type -> Type) -> Type -> Type
ItT s m = StateT (LeftToIterate s) (ReaderT (OriginalValues s) m)

runIterableT : Monad m => List s -> ItT s m a -> m a
runIterableT orig = runReaderT (MkOriginalValues orig) . evalStateT nothingLeft

namespace Compositions

  -- Ported from https://hackage.haskell.org/package/combinat-0.2.9.0/docs/src/Math.Combinat.Compositions.html
  -- Copyright of the original code: (c) 2008-2018 Balazs Komuves
  -- Original license is BSD-3-Clause.

  compositions' : List Nat -> Nat -> List $ List Nat
  compositions' []      0 = [[]]
  compositions' []      _ = []
  compositions' (s::ss) n =
    [ x::xs | x <- [0 .. min s n], xs <- compositions' ss (n `minus` x) ]

  compositions : Nat {-length-} -> Nat {-sum-} -> List $ List Nat
  compositions len d = compositions' (replicate len d) d where

  compositions1 : Nat {-len-} -> Nat {-sum-} -> List $ List Nat
  compositions1 len d = if len > d
    then []
    else map (+1) <$> compositions len (d `minus` len)

  export
  allCompositions1 : Nat -> List $ List $ List Nat
  allCompositions1 n = flip compositions1 n <$> [1..n]

namespace T

  public export
  data Tree = Leaf | Node (List Tree)

  export
  treesOfSize : Nat -> List Tree
  treesOfSize 0 = []
  treesOfSize 1 = [Leaf]
  treesOfSize (S n) = concatMap subtrees $ concat $ allCompositions1 n
    where
      combineLists : forall a. List (List a) -> List (List a)
      combineLists = sequence

      subtrees : List Nat -> List Tree
      subtrees = map Node . combineLists . map treesOfSize

data Tree a = Leaf a | Node (List $ Tree a)

Show a => Show (Tree a) where
  show (Leaf x) = "{" ++ show x ++ "}"
  show (Node ts) = "@(" ++ (concat $ map show ts) ++ ")"

decorateTree'' : Iterable'' a m => T.Tree -> m (Tree a)
decorateTree'' T.Leaf      = Leaf <$> next''
decorateTree'' (T.Node ts) = Node <$> traverse decorateTree'' ts

decoratedTreesIterator'' : Iterable'' a m => Iterable'' T.Tree m => Monad m => m (Tree a)
decoratedTreesIterator'' = next'' >>= decorateTree''

takeSome : Monad m => m a -> m $ List a
takeSome = sequence . replicate 6

t' : Iterable'' a (StateT (LeftToIterate T.Tree) (ReaderT (OriginalValues T.Tree) m)) => Monad m => m $ List $ Tree a
t' = runIterableT (T.treesOfSize 4) $ takeSome decoratedTreesIterator''

decoratedTreesExample'' : List $ Tree Int
--decoratedTreesExample'' =
--  runIdentity $
--    runIterableT {s=Int} [1..5] $ t'
    --  runIterableT (T.treesOfSize 4) $
    --    takeSome decoratedTreesIterator''
