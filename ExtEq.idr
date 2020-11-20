module ExtEq

infix 9 =~=

-- Universal (of any order) extensional equality
public export
(=~=) : {ty : Type} -> ty -> ty -> Type
(=~=) {ty = s -> _} a b = (x : s) -> a x =~= b x
(=~=)               a b =            a   =   b

public export
interface Functor m => FunctorExt m where
  0 map_ext : {f, g : a -> b} -> f =~= g -> map {f=m} f =~= map g

export
FunctorExt List where
  map_ext fg [] = ?foo_1
  map_ext fg (x::xs) = let fgx = fg x
                           sub = map_ext fg xs in
                       ?foo_2
