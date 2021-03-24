injToDec : {0 f : a -> b} -> ({0 x, y : a} -> f x = f y -> x = y) -> Dec (f x = f y) -> Dec (x = y)
injToDec inj $ Yes p = Yes $ inj p
injToDec _   $ No up = No $ up . cong f
