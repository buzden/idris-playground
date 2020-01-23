module PlusComm

%access export

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
muGenSucc = ?a_good_place_to_get_started

public export
Add : Conat -> Conat -> Conat
Add = ?can_be_implemented_differently_for_the_proof_ease_of_plus_commutative_law

-- Idris weak weak, partial implementation is allowed but there's random test
partial
plusCommutative : (a : Conat) -> (b : Conat) ->
                  Bisimulation (Add a b) (Add b a)
plusCommutative = ?this_was_mugen_plus_mugen_bisimulates_mugen_but_Idris_too_weak
