total
tailRecId : (a -> Either a b) -> a -> b
tailRecId f a with (f a)
  tailRecId f a | Left a2 = tailRecId f a2
  tailRecId f a | Right x = x
