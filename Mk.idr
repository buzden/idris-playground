import Language.Reflection

import Data.DPair

%default total

isTyCon : NameInfo -> Bool
isTyCon $ MkNameInfo $ TyCon {} = True
isTyCon _                       = False

mkImpl : TTImp -> Elab $ Exists $ \t => t
mkImpl expr = do
  let fc = getFC expr
  let IVar _ name = expr
    | IPrimVal {} => failAt fc "Expression must not be a primitive value or type"
    | expr        => failAt fc "Expression must be just a name"
  [(name, _)] <- getInfo name <&> filter (isTyCon . snd)
    | []      => failAt fc "Expression must be an unambiguous type"
    | _::_::_ => failAt fc "Given name `\{show name}` is ambiguous type"
  [conName] <- getCons name
    | []      => failAt fc "No constructors found for `\{show name}`"
    | _::_::_ => failAt fc "Given type `\{show name}` has more than one constructor"
  [(_, conType)] <- getType conName
    | cs => failAt fc "INTERNAL ERROR: Unable to get a type of the constructor `\{show conName}` (\{show $ length cs} constructors)"
  conType <- check {expected=Type} conType
  conExpr <- check {expected=conType} $ IVar fc conName
  pure $ Evidence conType conExpr

mkImpl' : (t : ty) -> Elab $ Exists $ \t => t
mkImpl' t = do
  expr <- quote t
  mkImpl expr

--export
--0 MkType : ty -> Elab Type
--MkType = map fst . mkImpl'
--
--export %macro
--Mk : (t : ty) -> Elab a
--Mk t = do
--  Evidence retTy x <- mkImpl' t
--  check !(quote x)

export %macro
Mk : (t : ty) -> Elab a
Mk t = do
  expr <- quote t
  let fc = getFC expr
  let IVar _ name = expr
    | IPrimVal {} => failAt fc "Expression must not be a primitive value or type"
    | expr        => failAt fc "Expression must be just a name"
  [(name, _)] <- getInfo name <&> filter (isTyCon . snd)
    | []      => failAt fc "Expression must be an unambiguous type"
    | _::_::_ => failAt fc "Given name `\{show name}` is ambiguous type"
  [conName] <- getCons name
    | []      => failAt fc "No constructors found for `\{show name}`"
    | _::_::_ => failAt fc "Given type `\{show name}` has more than one constructor"
  check $ IVar fc conName

%language ElabReflection

-- x = %runElab quote Show >>= mkImpl

aqShow = %runElab mkImpl' Show

showNat : Show Nat
showNat = snd aqShow (\n => show n) (\d, n => showPrec d n)

failing "Expression must not be a primitive value or type"

  y = %runElab mkImpl' String

failing "Expression must be just a name"

  y = %runElab mkImpl' (\x => List x)

failing "No constructors found for `Builtin.Void`"

  y = %runElab mkImpl' Void

failing "Given type `Prelude.Basics.List` has more than one constructor"

  y = %runElab mkImpl' List

aqShowNat : Show Nat
aqShowNat = Mk Show (\n => show n) (\d, n => showPrec d n)

aqShowNat' = Mk Show (\n : Nat => show n) (\d, n => showPrec d n)

aq : (a -> String) -> (Prec -> a -> String) -> Show a
aq = Mk Show

aq' = Mk Show (show . S)
