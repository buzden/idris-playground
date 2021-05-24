ff : (a -> b) -> Not (Not a) -> Not (Not b)
ff ab nna nb = nna $ nb . ab
