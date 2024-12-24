const : forall a, b. a -> b -> a
const x _ = x

const' : forall a. a -> (forall b. b) -> a
const' x _ = x

failing
  consts : forall a, b. (x : a) -> (y : b) -> Main.const x y = Main.const' x y
  consts x y = y

consts' : (x : a) -> (y : forall b. b) -> Main.const x y = Main.const' x y
consts' x y = y

