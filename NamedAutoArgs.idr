f : (a : Int) => Int
f @{x} = x

g : Int
g = f {a=4}

h : Int
h = f @{5}
