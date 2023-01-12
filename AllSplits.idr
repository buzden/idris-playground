import Data.Vect
import Data.Vect.Quantifiers

%default total

public export
allSplits : (l : List a) -> Vect (S $ length l) (List a, List a)
allSplits []           = [([], [])]
allSplits full@(x::xs) = ([], full) :: (mapFst (x::) <$> allSplits xs)

allMapped : {xs : Vect n a} -> All p xs -> All (p . f) (map f xs)

allSplitsAsSplits : (xs : List a) -> All (\(l, r) => l ++ r = xs) $ allSplits xs
allSplitsAsSplits []      = [Refl]
allSplitsAsSplits (x::xs) = let axs = allSplitsAsSplits xs in Refl :: (mapProperty (\xx => ?foo) $ allMapped {f=mapFst (x::)} axs)
