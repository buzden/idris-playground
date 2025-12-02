import Data.Fin
import Data.List

%default total

data T : (isRoot : Bool) -> Type where
  Leaf : T False
  Node : List (T False) -> T isRoot

replaceAt' : (xs : List a) -> (idx : Fin $ length xs) -> a -> List a

data Ops : T isRoot -> Type
finalState : {0 t : T isRoot} -> Ops t -> T isRoot

data Ops : T isRoot -> Type where
  End         : {t : _} -> Ops t
  ReplaceLeaf : (t : T False) -> (cont : Ops t) -> Ops Leaf
  AddToNode   : (t : T False) -> (cont : Ops (Node {isRoot} $ t :: xs)) -> Ops (Node {isRoot} xs)
  DiveIn      : (idx : Fin (length xs)) -> (subops : Ops (index' xs idx)) -> (cont : Ops $ Node {isRoot} $ replaceAt' xs idx $ finalState subops) -> Ops (Node {isRoot} xs)

finalState $ End {t}                = t
finalState (ReplaceLeaf x cont)     = finalState cont
finalState (AddToNode x cont)       = finalState cont
finalState (DiveIn idx subops cont) = finalState cont
