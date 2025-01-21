import Control.Monad.Identity
import Control.Monad.Reader

import Language.Reflection

%default total

-- Replaces `y` with `x` only in the top-level quoting context (ignoring `IQuoteDecl`)

f : MonadReader Nat m => (original : TTImp) -> (mapped : m TTImp) -> m TTImp
f v@(IVar fc nm) _ = pure $ if !ask == 0 && nm == `{y} then IVar fc `{x} else v
f (IQuote fc s) mapped = local S mapped
f (IUnquote fc expr) mapped = local (`minus` 1) mapped
f _ x = x

g : TTImp -> TTImp
g = runReader Z . mapATTImp' f

-- y + `(y + ~(x + y))
Expr : TTImp
Expr = `(y + `(y + ~(IUnquote EmptyFC `(x + y))))

-- x + `(y + ~(x + x))
Expr' : TTImp
Expr' = `(x + `(y + ~(IUnquote EmptyFC `(x + x))))

main : IO ()
main = do
  let before = show Expr
  let after = show $ g Expr
  let expected = show Expr'
  putStrLn "before: \{before}"
  putStrLn "after:  \{after}"
  putStrLn "as expected: \{show $ after == expected}"
