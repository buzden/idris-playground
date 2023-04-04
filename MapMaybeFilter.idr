import Data.Maybe

%default total

mapMaybeAsFilter : (condBool : a -> Bool) ->
                    (condMaybe : a -> Maybe a) ->
                    ((x : a) -> condBool x = isJust (condMaybe x)) ->
                    ((x, y : a) -> condMaybe x = Just y -> x = y) ->
                    (xs : List a) ->
                    mapMaybe condMaybe xs = filter condBool xs
mapMaybeAsFilter condBool condMaybe fRel cmProp [] = Refl
mapMaybeAsFilter condBool condMaybe fRel cmProp (x::xs) with (fRel x)
  _ | xx with (condMaybe x) proof cm | (condBool x)
    _ | Nothing | False = mapMaybeAsFilter condBool condMaybe fRel cmProp xs
    _ | Just y  | True  = do rewrite mapMaybeAsFilter condBool condMaybe fRel cmProp xs
                             rewrite cmProp x y cm
                             Refl
