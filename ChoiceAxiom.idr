-- Axiom of (constructive) choice

ch : {0 r : a -> b -> Type} -> ((x : a) -> (y : b ** r x y)) -> (f : a -> b ** (x : a) -> r x (f x))
ch f = (\x => fst (f x) ** \x => let _ = True in snd (f x))

-- The dummy `let` above is needed for typecheck success in idris-0.3.0, to be removed when fixed.
