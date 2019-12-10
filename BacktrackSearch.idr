module BacktrackSearch

import Data.So

%default total

data X = A | B | C

Eq X where
  A == A = True
  B == B = True
  _ == _ = False

data Statement : Type -> Type where
  MkStmt : (x : X) -> {auto nonA : So (x /= A)} -> Statement X

summon : {auto u : a} -> a
summon {u} = u

u : Statement X
u = MkStmt B

-- works and should
lastOfTwo : Statement X
lastOfTwo = let a = A; b = B in summon

-- works and should
theOnlyGood : Statement X
theOnlyGood = let b = B in summon

-- does not work, but why not? Why it stops searching after finding the first variant?
firstOfTwo : Statement X
firstOfTwo = let b = B; a = A in summon

-- should not work and does not
theOnlyBad : Statement X
theOnlyBad = let a = A in summon
