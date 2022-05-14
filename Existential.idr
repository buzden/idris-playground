import Data.Maybe

interface Expr m where
  val : Nat -> m Nat
  add : m Nat -> m Nat -> m Nat
  lt  : m Nat -> m Nat -> m Bool
  eq  : m Nat -> m Nat -> m Bool

record DocExpr a where
  constructor MkDocExpr
  strVal : String

Expr DocExpr where
  val n   = MkDocExpr $ show n
  add l r = MkDocExpr "(\{l.strVal}) + (\{r.strVal})"
  lt  l r = MkDocExpr "(\{l.strVal}) < (\{r.strVal})"
  eq  l r = MkDocExpr "(\{l.strVal}) == (\{r.strVal})"

namespace Any

  -- Universal quantification, `forall` is in the field of function type (negative, contravariant position)
  data ParseResult : Type -> Type where
    MkParseResult : (forall m. Expr m => Maybe $ m a) -> ParseResult a

  -- Creator cannot know anything about particular `m`, it has to use only operations from the interface
  parseBoolExpr : String -> ParseResult Bool
  parseBoolExpr _ = MkParseResult $ Just $ (val 0 `add` val 1) `lt` val 0

  -- User may decide a particular `m` which satisfies all the constraints,
  -- thus can use particular functions of particular implementation (`strVal` in this case).
  user : String
  user = case parseBoolExpr "lalala" of
           MkParseResult res => (fromMaybe (MkDocExpr "") res).strVal ++ "\n"

namespace Some

  -- Existential quantification, `forall` is in the constructor itself (positive, covariant position)
  data ParseResult : Type -> Type where
    MkParseResult : Expr m => Maybe (m a) -> ParseResult a

  -- Creator can define which particular implementation is used, thus it can do whatever this particular implementation allows
  parseBoolExpr : String -> ParseResult Bool
  parseBoolExpr _ = MkParseResult $ Just $ MkDocExpr "whatever you want"

  -- User knows only the fact that `m` implements `Expr` and may do only what's allowed by this interface
  user : String
  user = case parseBoolExpr "lalala" of
           MkParseResult res => do
             let x = fromMaybe (val 0 `eq` val 0) res
             "I can't do a lot of things with `x` :-("
