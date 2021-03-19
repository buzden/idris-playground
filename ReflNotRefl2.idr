module ReflNotRefl2

import Data.Fin

import ReflNotRefl1

prop : ind 3 (Undef {n=4} `W` (3, Just Y1)) = Just Y1
prop = Refl
