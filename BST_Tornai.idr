module BST_Tornai

import Data.So

import Syntax.WithProof

%default total

infix 6 <<, >>

namespace WithExplicitPredicates_So

  -- not so effective solution, but easier to be understood for liquidhaskellers, I think

  data BST : (a : Type) -> Ord a -> Type
  (<<) : a -> BST a ord -> Bool
  (>>) : a -> BST a ord -> Bool

  data BST : (a : Type) -> Ord a -> Type where
    Leaf : BST a o
    Node : (o : Ord a) => (k : a) -> (l : BST a o) -> (r : BST a o) -> So (k >> l) -> So (k << r) -> BST a o

  x << Leaf = True
  x << (Node k _ Leaf             _ _) = x < k
  x << (Node k l (Node _ _ _ _ _) _ _) = x << l

  x >> Leaf = True
  x >> (Node k Leaf             _ _ _) = x > k
  x >> (Node k (Node _ _ _ _ _) r _ _) = x >> r

  insert : (o : Ord a) => (x : a) -> BST a o -> BST a o

  insertPresL : (o : Ord a) => {x, j : a} -> {t : BST a o} ->
                So (x < j) -> So (j >> l) -> So (j >> insert x t)
  insertPresR : (o : Ord a) => {x, j : a} -> {t : BST a o} ->
                So (x > j) -> So (j << l) -> So (j << insert x t)

  insert x Leaf = Node x Leaf Leaf Oh Oh
  insert x n@(Node k l r kMoreL kLessR) with (x < k) proof xLessK
    _ | True = Node k (insert x l) r (insertPresL (eqToSo xLessK) kMoreL) kLessR
    _ | False with (x > k) proof xMoreK
      _ | True = Node k l (insert x r) kMoreL (insertPresR (eqToSo xMoreK) kLessR)
      _ | False = n

  -- Long-long proofs, left to the reader
  -- One particular complexity is quadratic notion of `>>` and `<<` checks
  insertPresL y z = ?insertPresL_rhs
  insertPresR y z = ?insertPresR_rhs

namespace WithExplicitPredicates_Inductive

  data BST : (a : Type) -> Ord a -> Type
  data (<<) : a -> BST a o -> Type
  data (>>) : a -> BST a o -> Type

  data BST : (a : Type) -> Ord a -> Type where
    Leaf : BST a o
    Node : (o : Ord a) => (k : a) -> (l : BST a o) -> (r : BST a o) -> k >> l -> k << r -> BST a o

  data (<<) : a -> BST a o -> Type where
    LL : x << Leaf
    LP : (o : Ord a) => {0 l : BST a o} -> {0 kl : k >> l} -> {0 kr : k << Leaf} ->
         So (x < k) -> x << Node k l Leaf kl kr
    LN : (o : Ord a) => {0 l, l', r' : BST a o} -> {0 kl : k >> l} -> {0 kl' : k' >> l'} -> {0 kr' : k' << r'} ->
         {0 kr : k << Node k' l' r' kl' kr'} ->
         x << l -> x << Node k l (Node k' l' r' kl' kr') kl kr

  data (>>) : a -> BST a ord -> Type where

  -- unfinished

namespace WithTypeParams

  data BdTree : (a : Type) -> Ord a -> (min : a) -> (max : a) -> Type where
    Leaf : (o : Ord a) => (k : a) -> BdTree a o k k
    NL   : (o : Ord a) => (k : a) -> (l : BdTree a o lmin lmax) -> (0 _ : So (lmax < k)) -> BdTree a o lmin k
    NR   : (o : Ord a) => (k : a) -> (r : BdTree a o rmin rmax) -> (0 _ : So (k < rmin)) -> BdTree a o k rmax
    NLR  : (o : Ord a) => (k : a) -> (l : BdTree a o lmin lmax) -> (r : BdTree a o rmin rmax) ->
           (0 _ : So (lmax < k)) -> (0 _ : So (k < rmin)) -> BdTree a o lmin rmax

  minLTEmax : (o : Ord a) => BdTree a o mi ma -> mi <= ma = True -- true only when `<=` is coherent with `<` and `=` is reflexive

  %hide Prelude.EqOrd.min
  %hide Prelude.EqOrd.max

  max : Ord a => a -> a -> a
  max x y = if y < x then x else y

  min : Ord a => a -> a -> a
  min x y = if x < y then x else y

  -- These must be an additional requirement to `Ord`, but I'm declaring it with no body for simplicity
  rev : Ord a => {0 x, y : a} -> x < y = False -> y < x = True
  trans_o  : Ord a => {0 x, y, z : a} -> x < y = True -> y < z = True -> x < z = True
  trans_el : Ord a => {0 x, y, z : a} -> x <= y = True -> y < z = True -> x < z = True
  trans_er : Ord a => {0 x, y, z : a} -> x < y = True -> y <= z = True -> x < z = True

  insert' : (o : Ord a) => (x : a) -> BdTree a o mi ma -> BdTree a o (mi `min` x) (x `max` ma)
  insert' x (Leaf k) with (k < x) proof kx
    _ | True  = NR k (Leaf x) (eqToSo kx)
    _ | False = NL k (Leaf x) (eqToSo $ rev kx)
  insert' x (NL k {lmax} l kg) with (k < x) proof kx
    _ | True  = rewrite the (mi < x = True) $ minLTEmax (NL k l kg) `trans_el` kx in
                NLR k l (Leaf x) kg (eqToSo kx)
    _ | False = let newL = insert' x l in
                NL k newL $ case @@ (lmax < x) of
                              (True  ** prf) => rewrite prf in eqToSo $ rev kx
                              (False ** prf) => rewrite prf in kg
  insert' x (NR k r kl) = ?insert'_rhs_3
  insert' x (NLR k l r kg kl) = ?insert'_rhs_4

  data BST : Type -> Type where
    Empty : BST a
    NonEmpty : BdTree a o min max -> BST a
