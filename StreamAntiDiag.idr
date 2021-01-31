module StreamAntiDiag

import Data.List
import Data.Nat
import Data.Stream
import Data.Stream.Extra

antidiag2 : Stream a -> Stream b -> Stream (a, b)
antidiag2 xs ys = map (bimap (flip index xs) (flip index ys)) $ flattenStreamOfLists $ allSums <$> iterate S Z
  where
    allSums : Nat -> List (Nat, Nat)
    allSums n = iterateN n (\(a, b) => (S a, pred b)) (0, n)

    flattenStreamOfLists : forall a. Stream (List a) -> Stream a
    flattenStreamOfLists (xs::xxs) = startWith xs $ flattenStreamOfLists xxs

antidiag2With : (a -> b -> c) -> Stream a -> Stream b -> Stream c
antidiag2With f = map (uncurry f) .: antidiag2

-- Applicative's `(<*>) = antidiag2With apply` wouldn't satisfy `pure id <*> v = v` when `pure = repeat`.
