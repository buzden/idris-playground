%default total

f : {k : _} -> (a : k) -> Bool
f Nat = False
f Z   = False
f _   = True

f_Nat : f Nat = False
f_Nat = Refl

f_Z : f Z = False
f_Z = Refl

f_S : f (S Z) = True
f_S = Refl

f_str : f "foo" = True
f_str = Refl

f_List_a : f (List a) = True
f_List_a = Refl

f_fun : f S = True
f_fun = ?f_fun_rhs

f_Type : f Type = True
f_Type = ?f_Type_rhs

f_List : f List = True
f_List = ?f_List_rhs
