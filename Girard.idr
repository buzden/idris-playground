-- Idea taken from http://liamoc.net/posts/2015-09-10-girards-paradox.html

%default total

data Set : Type where
  MkSet : (x : Type) -> (x -> Set) -> Set

In : Set -> Set -> Type
In a (MkSet _ f) = (x ** a = f x)

D : Set
D = MkSet (s ** Not $ s `In` s) fst

xind : x `In` D -> Not $ x `In` x
xind ((_ ** f) ** Refl) = f

xinx : {x : _} -> Not (x `In` x) -> x `In` D
xinx f = ((_ ** f) ** Refl)

dnotind : Not $ D `In` D
dnotind dind = xind dind dind

falso : Void
falso = dnotind $ xinx dnotind
