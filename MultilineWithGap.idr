s : String
s = """
  First line

  Third line
  """

ss : String
ss = "First line\nThird line"

sss : Main.s = Main.ss
sss = Refl

prS : IO ()
prS = putStrLn s

t : String
t = """
  First line
  
  Third line
  """

tt : String
tt = "First line\n\nThird line"

ttt : Main.t = Main.tt
ttt = Refl

prT : IO ()
prT = putStrLn t
