import Language.Reflection
import Language.Reflection.Types
import Language.Reflection.Pretty

import Text.PrettyPrint.Bernardy.Interface

data Y : Nat -> Type
data Z : Nat -> Nat -> Type
data B : (x : Nat) -> Y x -> Nat -> Type

data X : Type where
  MkY : (y : Y a) -> Z a b -> B a y c -> X

%language ElabReflection

f : Elab Decl
f = do
  [(nm, expr)] <- getType `{MkY}
    | _ => fail "too many variants"
  pure $ IClaim EmptyFC MW Private [] $ MkTy EmptyFC EmptyFC nm expr

main : IO ()
main = do
  putPretty $ `[MkY : (y : Y a) -> Z a b -> B a y c -> X] ++ [%runElab f]
