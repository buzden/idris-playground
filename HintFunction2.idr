import Data.Fuel

import HintFunctionGen

export %hint
ff : Fuel -> Gen Fuel
ff = pure

tn : Fuel -> Nat
tn Dry = Z
tn $ More x = S $ tn x

--------------

y : Fuel -> Gen Fuel
y = %search

Y : Gen Nat
Y = map tn $ y $ limit 20

Y_val : Y === pure 20
Y_val = Refl

--------------

export %hint
ff' : Gen Fuel
ff' = pure Dry

z : Fuel -> Gen Fuel
z = %search

Z : Gen Nat
Z = map tn $ z $ limit 20

Z_val : Z === pure 0 -- should be 20 instead of 0, as above
Z_val = Refl
