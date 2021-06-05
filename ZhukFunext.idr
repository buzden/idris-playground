-- Code modified from Alex Zhukovsky's one from DepTyp telegram chat (https://t.me/c/1062361327/39965)
-- Code modifiation is mostly a further usage of function extensionality.

record State s a where
 constructor MkState
 runState : s -> (a,s)

funext : {0 f, g : a -> b} -> ((x : a) -> f x = g x) -> f = g
funext = believe_me

injectiveProjections : (0 ab : (a,b)) -> (fst ab, snd ab) = ab
injectiveProjections {ab=(x,y)} = Refl

stateMap : (a -> b) -> (s -> (a, s)) -> s -> (b, s)
stateMap f = (mapFst f .)

stateMapIdIsId : stateMap Prelude.id rs = rs
stateMapIdIsId = funext \x => rewrite sym $ injectiveProjections $ rs x in Refl

Functor (State s) where
 map f (MkState rs) = MkState $ stateMap f rs

interface Functor f => VerifiedFunctor (0 f : Type -> Type) where
  functorIdentity : {0 a : Type} -> map {f} {a} Prelude.id = Prelude.id

VerifiedFunctor (State s) where
  functorIdentity = funext \(MkState _) => cong MkState stateMapIdIsId
