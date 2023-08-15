import Data.Fin
import Data.List

%default total

data Gen : Type -> Type where
  Pure : a -> Gen a
  Comp : (a -> b -> c) -> Gen a -> Gen b -> Gen c
  Alt  : List (Gen a) -> Gen a

data GenDesc : Gen a -> Type where
  P : GenDesc $ Pure x
  C : GenDesc ga -> GenDesc gb -> GenDesc $ Comp f ga gb
  A : (idx : Fin $ length ls) -> GenDesc (index' ls idx) -> GenDesc $ Alt ls

data GenDesc' : a -> Gen a -> Type where
  P' : GenDesc' x $ Pure x
  C' : GenDesc' x ga -> GenDesc' y gb -> GenDesc' (f x y) $ Comp f ga gb
  A' : (idx : Fin $ length ls) -> GenDesc' x (index' ls idx) -> GenDesc' x $ Alt ls
