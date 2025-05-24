import Data.So

%default total

ll : (p : a -> Bool) -> (xs : List a) -> Not $ So $ foldl (\acc, elem => acc && p elem) False xs
ll p (x::xs) s = ll p xs s

filterAll : (p : a -> Bool) -> (xs : List a) -> (So $ all p xs) => filter p xs = xs
filterAll p []           = Refl
filterAll p (x::xs) @{s} with (p x)
  filterAll p (x::xs) @{s} | True  = rewrite filterAll p xs in Refl
  filterAll p (x::xs) @{s} | False = absurd $ ll p xs s
