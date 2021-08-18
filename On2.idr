module On2

on2 : forall f, t. (t a -> t b -> c) -> (forall z. f z -> t z) -> f a -> f b -> c
on2 g h = \x, y => h x `g` h y
