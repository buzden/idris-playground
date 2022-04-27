module UseMapN

import Data.Vect

import MapN

%default total

data A a b c = MkA a b c

namespace Pure

  namespace SimpleTypes

    f1 : A Nat String Char
    f1 = mapN (MkA 5 "4") 'a'

    f2 : String -> Char -> A Nat String Char
    f2 s k = mapN (MkA 5) (s, k)

    f3 : Nat -> String -> Char -> A Nat String Char
    f3 n s k = mapN MkA (n, s, k)

namespace Monadic

  namespace AllM

    fm1 : Nat -> String -> Maybe Char -> Maybe $ A Nat String Char
    fm1 n s k = mapN (MkA n s) k

    fm2 : Nat -> Maybe String -> Maybe Char -> Maybe $ A Nat String Char
    fm2 n s k = mapN (MkA n) (s, k)

    fm3 : Maybe Nat -> Maybe String -> Maybe Char -> Maybe $ A Nat String Char
    fm3 n s k = mapN MkA (n, s, k)

  namespace MixWithPure

    fx2_1 : Nat -> String -> Maybe Char -> Maybe $ A Nat String Char
    fx2_1 n s k = mapN (MkA n) (s, k)

    fx3_1 : Nat -> Maybe String -> Maybe Char -> Maybe $ A Nat String Char
    fx3_1 n s k = mapN MkA (n, s, k)

    fx2_2 : Nat -> Maybe String -> Char -> Maybe $ A Nat String Char
    fx2_2 n s k = mapN (MkA n) (s, k)

    fx3_2 : Maybe Nat -> String -> Maybe Char -> Maybe $ A Nat String Char
    fx3_2 n s k = mapN MkA (n, s, k)

    fx3_3 : Maybe Nat -> Maybe String -> Char -> Maybe $ A Nat String Char
    fx3_3 n s k = mapN MkA (n, s, k)

  namespace MixWithTraversable

    ft3_1 : List Nat -> Maybe String -> Maybe Char -> Maybe $ List $ A Nat String Char
    ft3_1 n s k = mapN MkA (n, s, k)

    ft3_2 : Maybe Nat -> List String -> Maybe Char -> Maybe $ List $ A Nat String Char
    ft3_2 n s k = mapN MkA (n, s, k)

    ft3_3 : Maybe Nat -> Maybe String -> List Char -> Maybe $ List $ A Nat String Char
    ft3_3 n s k = mapN MkA (n, s, k)

    ft3_1_2 : List Nat -> List String -> Maybe Char -> Maybe $ List $ List $ A Nat String Char
    ft3_1_2 n s k = mapN MkA (n, s, k)

    --ft3_1_2' : List Nat -> List String -> Maybe Char -> Maybe $ List $ A Nat String Char
    --ft3_1_2' n s k = mapN MkA (n, s, k)

    ft3_1_3 : List Nat -> Maybe String -> List Char -> Maybe $ List $ List $ A Nat String Char
    ft3_1_3 n s k = mapN MkA (n, s, k)

    --ft3_1_3' : List Nat -> Maybe String -> List Char -> Maybe $ List $ A Nat String Char
    --ft3_1_3' n s k = mapN MkA (n, s, k)

    ft3_2_3 : Maybe Nat -> List String -> List Char -> Maybe $ List $ List $ A Nat String Char
    ft3_2_3 n s k = mapN MkA (n, s, k)

    ft3_2_3' : Maybe Nat -> List String -> List Char -> Maybe $ List $ A Nat String Char
    ft3_2_3' n s k = mapN MkA (n, s, k)

    ft3_1_2_3 : List Nat -> List String -> List Char -> Maybe $ List $ List $ List $ A Nat String Char
    ft3_1_2_3 n s k = mapN MkA (n, s, k)

    ft3_1_2_3' : List Nat -> List String -> List Char -> Maybe $ List $ List $ A Nat String Char
    ft3_1_2_3' n s k = mapN MkA (n, s, k)

    ft3_1_2_3'' : List Nat -> List String -> List Char -> Maybe $ List $ A Nat String Char
    ft3_1_2_3'' n s k = mapN MkA (n, s, k)

namespace Pure

  namespace FancyTypes

    eqIdx : Eq a => Fin n -> Vect n a -> Vect n a -> Bool
    eqIdx i = (==) `on` index i

    ff1 : Eq a => Fin n -> Vect n a -> Vect n a -> Bool
    ff1 i xs ys = mapN (eqIdx i xs) ys

    ff2 : Eq a => Fin n -> Vect n a -> Vect n a -> Bool
    ff2 i xs ys = mapN (eqIdx i) (xs, ys)

    ff3 : Eq a => Fin n -> Vect n a -> Vect n a -> Bool
    ff3 i xs ys = mapN eqIdx (i, xs, ys)

namespace DPair

  export
  minusLT : (n, m : Nat) -> m `LTE` n -> Nat
  minusLT n m _ = minus n m

  d1 : (n, m : Nat) -> m `LTE` n -> Nat
  d1 n m lte = mapN (minusLT n m) lte -- trivial case, no actual dpair

  d2 : (n, m : Nat) -> m `LTE` n -> Nat
  d2 n m lte = mapN {i=(m ** m `LTE` n)} (minusLT n) (m ** lte)

  d3 : (n, m : Nat) -> m `LTE` n -> Nat
  d3 n m lte = mapN {i=(n ** m ** LTE m n)} minusLT (n ** m ** lte)
