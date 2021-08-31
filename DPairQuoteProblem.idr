module DPairQuoteProblem

import Language.Reflection

%default total

extract : Type -> Elab Unit
extract ty = logTerm "debug.elab" 0 "type" !(quote ty)

%macro
extract' : Type -> Elab Unit
extract' = extract -- logTerm "debug.elab" 0 "type" !(quote ty)

%language ElabReflection

-----------------------------
--- One-parameter example ---
-----------------------------

namespace OneParameter

  data Y : Nat -> Type where
    Y0 : Y 0
    Y1 : Y 1

  %runElab logMsg "debug.elab" 0 "----------------------"
  namespace NonInlined

    X : Type
    X = (n : Nat ** Y n)

    %runElab extract X

    v : Unit
    v = %runElab extract X

    u : Unit
    u = extract' X

  %runElab logMsg "debug.elab" 0 "----------------------"
  namespace Inlined

    -- When there are not so many stuff inside the dpair, all is okay being inlined

    %runElab extract (n : Nat ** Y n)

    v : Unit
    v = %runElab extract (n : Nat ** Y n)

    u : Unit
    u = extract' (n : Nat ** Y n)

-----------------------------
--- Two-parameter example ---
-----------------------------

namespace TwoParameters

  data Y : Nat -> Type -> Type where
    Y0 : Y 0 Int
    Y1 : Y 1 Nat

  %runElab logMsg "debug.elab" 0 "----------------------"
  namespace NotInlined

    -- The following two elaboration runnings log the same result:

    X : Type
    X = (n : Nat ** x : Type ** Y n x)

    %runElab extract X

    v : Unit
    v = %runElab extract X

    u : Unit
    u = extract' X

  %runElab logMsg "debug.elab" 0 "----------------------"
  namespace Inlined

    -- The following two elaboration runnings log different results,
    -- but we expect them to be the same as above.


    %runElab extract (n : Nat ** x : Type ** Y n x)

    v : Unit
    v = %runElab extract (n : Nat ** x : Type ** Y n x)

    u : Unit
    u = extract' (n : Nat ** x : Type ** Y n x)
