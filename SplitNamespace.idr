namespace X

  f : Int -> Int

  export
  f_pub : Int -> Int
  f_pub = f

namespace Y

  g : Int -> Int -> Int
  g x y = x + f_pub y

namespace X

  f 5 = 6
  f x = x - 1
