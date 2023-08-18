module Main

import Data.List1
import Data.Vect

import Hedgehog

import Language.Reflection
import Language.Reflection.Derive
import Language.Reflection.Syntax
import Language.Reflection.Types

[FnStub] Show (Nat -> Nat) where
  show _ = "<fn>"

print_a_fun_ : Property
print_a_fun_ = property $ do
  fn <- forAll @{FnStub} $ function_ $ nat $ constant 0 999
  let domain : List _ := [0, 1, 2, 3, 100, 1000, 10000, 100000, 10000000, 100000000]
  let codomain = fn <$> domain
  annotate "args: \{show domain}"
  annotate "vals: \{show codomain}"
  assert False -- to print annotations

badFn_Prop : Property
badFn_Prop = property $ do
  fn <- forAll @{FnStub} $ function_ $ nat $ constant 0 999
  n  <- forAll $ nat $ constant 0 1000000000
  assert $ fn n >= 100

niceFn_Prop : Property
niceFn_Prop = property $ do
  natList <- forAll $ list (constant 1 10) $ nat $ constant 0 99
  fn <- forAll @{FnStub} $ function_ $ nat $ constant 100 999
  let newList = map fn natList
  annotate $ show newList
  assert $ all (>= 100) newList

----------------------------------------------------

print_a_fun : Property
print_a_fun = property $ do
  fn <- forAll $ function $ nat $ constant 0 999
  let domain : List Nat = [0, 1, 2, 3, 100, 1000, 10000, 100000, 10000000, 100000000]
  let codomain = apply fn <$> domain
  annotate "args: \{show domain}"
  annotate "vals: \{show codomain}"
  assert False -- to print annotations

print_a_fun_fun : Property
print_a_fun_fun = property $ do
  fn <- forAll $ function $ nat $ constant 0 999
  let fn = apply fn
  let domain : List Nat = [0, 1, 2, 3, 100, 1000, 10000, 100000, 10000000, 100000000]
  let codomain = fn <$> domain
  annotate "args: \{show domain}"
  annotate "vals: \{show codomain}"
  assert (fn 0 == 0)

print_a_fun_list_fun : Property
print_a_fun_list_fun = property $ do
  fn <- forAll $ function $ nat $ constant 0 999
  let fn = apply fn
  let domain : List (List Nat) = [[], [0], [1], [0, 1], [1, 0]]
  let codomain = fn <$> domain
  annotate "args: \{show domain}"
  annotate "vals: \{show codomain}"
  assert (fn [1] == 0)

niceFnProp : Property
niceFnProp = property $ do
  natList <- forAll $ list (constant 1 10) $ nat $ constant 0 99
  fn <- forAll $ function $ nat $ constant 100 999
  let newList = map (apply fn) natList
  annotate $ show newList
  assert $ all (>= 100) newList

badFnProp : Property
badFnProp = property $ do
  fn <- forAll $ function $ nat $ constant 0 999
  n  <- forAll $ nat $ constant 0 1000000000
  assert $ apply fn n >= 100

----------------------------------------------------

%language ElabReflection

data X = A | B Nat | C String

%runElab derive "X" [Cogen]

data Y a = YA a | YB X | YC (Y a) (Y Nat)

%runElab derive "Y" [Cogen]

%runElab derivePattern "Vect" [I, P] [Cogen]

data Z : Nat -> Type -> Type where
  Z1 : Z 1 a
  Z2 : Y a -> Vect n (Z n a) -> Z (S n) a

%runElab derivePattern "Z" [I, P] [Cogen]

print_z_fun : Property
print_z_fun = property $ do
  fn <- forAllWith (const "<fn>") $ dargfun_ {b = \n => Z n String} $ nat $ constant 0 100
  annotate "fn Z1 = \{show $ fn Z1}"
  annotate "fn (Z2 (YA \"foo\") [Z1]) = \{show $ fn (Z2 (YA "foo") [Z1])}"
  annotate "fn (Z2 (YA \"lala\") [Z1]) = \{show $ fn (Z2 (YA "lala") [Z1])}"
  assert $ fn Z1 == 0 || fn (Z2 (YA "lala") [Z1]) == 0

main : IO Unit
main = test
  [ "`function_`" `MkGroup`
    [ ("print function_", print_a_fun_)
    , ("bad function_", badFn_Prop)
    , ("nice function_", niceFn_Prop)
    ]
  , "`function`" `MkGroup`
    [ ("print function", print_a_fun)
    , ("print funny function", print_a_fun_fun)
    , ("print funny list function", print_a_fun_list_fun)
    , ("bad function", badFnProp)
    , ("nice function", niceFnProp)
    ]
  , "cogen derivation" `MkGroup`
    [ ("print Z function", print_z_fun)
    ]
  ]
