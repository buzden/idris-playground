import Language.Reflection

%language ElabReflection

%macro
coolMacro : Nat -> Elab (Nat -> Nat)
coolMacro n = lambda Nat $ \m => pure $ n + m + 1

Cool_indirect : Nat
Cool_indirect = let z = coolMacro 4 in z 5

Cool_direct : Nat
Cool_direct = coolMacro 4 5

cool_eq : Cool_indirect = Cool_direct
cool_eq = Refl

cool_eq' : Cool_indirect ~=~ coolMacro 4 5
cool_eq' = Refl

Cool_direct' : ?
Cool_direct' = coolMacro 4 5

cool_eq'' : Cool_indirect ~=~ Cool_direct'
cool_eq'' = Refl

%macro
depMacro : (b : Bool) -> if b then Elab (Nat -> Nat) else Nat -> Elab Nat
depMacro False = \m => pure $ m + 100
depMacro True  = lambda Nat $ \m => pure $ m + 200

Dep_indirect_t : Nat
Dep_indirect_t = let z = depMacro True in z 5

Dep_direct_t : Nat
Dep_direct_t = depMacro True 5

dep_t : Dep_indirect_t = Dep_direct_t
dep_t = Refl

dep_t' : Dep_indirect_t ~=~ depMacro True 5
dep_t' = Refl

Dep_indirect_f : Nat
Dep_indirect_f = let z = depMacro False 5 in z

Dep_direct_f : Nat
Dep_direct_f = depMacro False 5

dep_f : Dep_indirect_f = Dep_direct_f
dep_f = Refl

dep_f' : Dep_indirect_f ~=~ depMacro False 5
dep_f' = Refl
