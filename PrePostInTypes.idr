data A : Type
data B : Type
data C : B -> Type
data D : Type

f : A -> (b : B) -> C b -> D

data Pred : A -> (b : B) -> C b -> Type
data Post : A -> (b : B) -> C b -> D -> Type

prop : (a : A) -> (b : B) -> (c : C b) -> Pred a b c -> Post a b c (f a b c)

f' : (a : A) -> (b : B) -> (c : C b) -> Pred a b c -> (d : D ** Post a b c d)
