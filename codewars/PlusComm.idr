module PlusComm

%access export
%default total

namespace Conat
  %access public export

  codata Conat : Type where
    Coz : Conat
    Cos : Conat -> Conat

  codata Bisimulation : Conat -> Conat -> Type where
    Biz : Bisimulation Coz Coz
    Bis : {a : Conat} -> {b : Conat} ->
          (Bisimulation a b) ->
          (Bisimulation (Cos a) (Cos b))

  MuGen : Conat
  MuGen = Cos MuGen

muGenSucc : Bisimulation (Cos MuGen) MuGen
muGenSucc = Bis muGenSucc

public export
Add : Conat -> Conat -> Conat
Add Coz     Coz     = Coz
Add (Cos a) Coz     = Cos a
Add Coz     (Cos b) = Cos b
Add (Cos a) (Cos b) = Cos $ Cos $ Add a b

biX : (x : Conat) -> Bisimulation x x
biX Coz     = Biz
biX (Cos x) = Bis $ biX x

total
plusCommutative : (a : Conat) -> (b : Conat) -> Bisimulation (Add a b) (Add b a)
plusCommutative Coz     Coz     = Biz
plusCommutative Coz     (Cos y) = biX $ Cos y
plusCommutative (Cos x) Coz     = biX $ Cos x
plusCommutative (Cos x) (Cos y) = Bis $ Bis $ plusCommutative x y
