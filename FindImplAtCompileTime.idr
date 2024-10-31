import Language.Reflection

%default total

interface X (0 str : String) where
  f : List Nat -> List Nat

scr : String -> Elab $ List Nat
scr s = do
  Just impl <- search $ X s
    | Nothing => logMsg "find-impl" 0 "`X` for \{s} was not found" $> []
  let arg : List Nat = [1, 2, 3]
--  xs : List Nat <- check `(f @{the (X ~ !(quote s)) %search} ~ !(quote arg))
  xs : List Nat <- check `(f @{~ !(quote impl)} ~ !(quote arg))
  logMsg "find-impl" 0 "`X` for \{s} was found"
  --logMsg "find-impl" 0 "the result is: \{show xs}"
  for_ xs $ \x => logMsg "find-impl.item" 0 "item \{show x}"
  pure xs

%language ElabReflection

L1 : List Nat
L1 = %runElab scr "should not find"

l1_corr : L1 = []
l1_corr = Refl

L2 : List Nat
L2 = %runElab scr "find later"

l2_corr : L2 = []
l2_corr = Refl

namespace Sub

  export
  X "find later" where
    f = map (+1)

L3 : List Nat
L3 = %runElab scr "find later"

l3_corr : L3 = [2, 3, 4]
l3_corr = Refl

L3' : List Nat
L3' = f @{the (X "find later") %search} [1, 2, 3]

l3'_corr : L3' = [2, 3, 4]
l3'_corr = Refl
