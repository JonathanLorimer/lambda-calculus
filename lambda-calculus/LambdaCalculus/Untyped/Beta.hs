module LambdaCalculus.Untyped.Beta where

import Data.Functor.Foldable
import Data.Monoid (All (..))
import Data.Set qualified as S
import LambdaCalculus.Untyped.Alpha (RenameError, safeAlphaRename)
import LambdaCalculus.Untyped.Expr
import LambdaCalculus.Untyped.Vars (Produce (..), fv, isFreeIn, vars)

-- x :: a
-- M N :: Expr a
-- Redex      = App (Abs x M) N  ~ (λx . M) N
-- Contractum = subst M x N      ~ M [x := N ]
subst ::
  (Ord a, Produce a) =>
  a -> -- x
  Expr a -> -- M
  Expr a -> -- N
  Either (RenameError a) (Expr a)
subst var m n = do
  renamePass <- flip cataA m \case
    VarF a -> pure $ Var a
    AppF expr1 expr2 -> liftA2 App expr1 expr2
    AbsF a eitherExpr -> do
      expr <- eitherExpr
      if not (a `isFreeIn` n) || not (var `isFreeIn` expr)
        then pure $ Abs a expr
        else do
          let a' = next (fv n `S.union` vars expr)
          newExpr <- safeAlphaRename expr (fv expr) a a'
          pure $ Abs a' newExpr
  pure $ flip cata renamePass \case
    VarF a ->
      if a == var
        then n -- x[x := N ] ≡ N
        else Var a -- y[x := N ] ≡ y if x !≡ y
    AppF expr1 expr2 -> App expr1 expr2
    AbsF a expr1 -> Abs a expr1

isNF :: Expr a -> Bool
isNF =
  getAll . para \case
    VarF _ -> All True
    AppF (Abs _ _, _) (_, _) -> All False
    AppF (_, a1) (_, a2) -> a1 <> a2
    AbsF _ (_, a1) -> a1
