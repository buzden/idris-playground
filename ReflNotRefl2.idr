module ReflNotRefl2

import Data.Fin

import ReflNotRefl1

prop : ind 3 (Undef {n=4} `W` (3, True)) = True
prop = Refl
