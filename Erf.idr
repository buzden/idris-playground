module Erf

export
%foreign "C:erf, libm 6"
erf : Double -> Double

export
%foreign "C:erfc, libm 6"
erfc : Double -> Double
