-- This code is based on some code by Madman Bob as by answer for him on Discord:
-- https://discord.com/channels/827106007712661524/1092808994629894195/1092824330485907598

import Data.List.Elem
import Decidable.Equality

import Language.Reflection

%default total

record Syntax where
    constructor MkSyntax
    ops : List String

record Op (nm : String) (0 syn : Syntax) where
    constructor MkOp
    idx : Elem nm syn.ops

name : {syn : Syntax} ->
       Op nm syn ->
       String
name (MkOp idx) = get syn.ops idx

%macro
operation : {syn : Syntax} ->
            (nm : String) ->
            Elab (Op nm syn)
operation nm = do
  IHole _ _ <- quote syn
    | _ => case isElem nm syn.ops of
             Yes idx => pure $ MkOp idx
             No _ => fail "\{show nm} not in \{show syn.ops}"
  Just so <- search (s : Syntax ** Op nm s)
    | Nothing => fail "couldn't find appropriate `Syntax` for given operation \{show nm}"
  Just eq <- search (syn === so.fst)
    | Nothing => fail "couldn't match hole and found syn"
  pure $ case eq of Refl => so.snd

%hint
MonoidSyntax : Syntax
MonoidSyntax = MkSyntax ["0", "+"]

%hint
GroupSyntax : Syntax
GroupSyntax = MkSyntax ["e", "*", "inv"]

%language ElabReflection

x : String
x = name $ operation {syn = GroupSyntax} "*"

Y : String
Y = name $ operation "*"

yCorr : Y = "*"
yCorr = Refl
