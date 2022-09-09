module NamedRes

import Data.List
import Data.Maybe

%default total

namespace Labelling

  public export
  Label : Type
  Label = String

  public export
  PresentLabel : List (Label, Type) -> Label -> Type
  PresentLabel ls l = IsJust (lookup l ls)

  public export
  TypeOf : (ls : List (Label, Type)) -> (l : Label) -> (0 _ : PresentLabel ls l) => Type
  TypeOf ls l with (lookup l ls)
    _ | Just ty = ty

infix 6 <==

public export
data FComp : (Type -> Type) -> List (Label, Type) -> Type -> Type where
  (<==) : (l : Label) -> f a -> FComp f [(l, a)] a
  -- Add a requirement that `ls` and `rs` do not intersect?
  (>>) : FComp f ls a -> FComp f rs b -> FComp f (ls ++ rs) b

-- Add a requirement that `l` and `r` differ?
export
wrapPair : (l, r : Label) -> f (a, b) -> FComp f [(l, a), (r, b)] (a, b)

export
passThrough2 : (f a -> f b -> f (a, b)) -> FComp f ls a -> FComp f rs b -> FComp f (ls ++ rs) (a, b)

-- could be `f a -> f (g b)`, but we need to change a mapping of appropriate label from `a` to `b`, but we don't know which one.
export
passThroughAny : Functor g => (f a -> f (g a)) -> FComp f ls a -> FComp f ls (g a)

namespace Use

  public export
  data FCompUsage : (Type -> Type) -> List (Label, Type) -> Type -> Type where
    Pure  : a -> FCompUsage f ls a
    (<*>) : FCompUsage f ls (a -> b) -> (l : Label) -> PresentLabel ls l => FCompUsage f ls b

  public export
  pure : a -> FCompUsage f ls a
  pure = Pure

  namespace ShowTypecheck

    f1 : FCompUsage Maybe [("a", Nat)] Integer
    f1 = [| natToInteger "a" |]

    f2 : FCompUsage Maybe [("a", Nat), ("b", Nat)] Nat
    f2 = [| plus "a" "b" |]

  export
  discharge : FComp f ls anything -> FCompUsage f ls a -> f a
