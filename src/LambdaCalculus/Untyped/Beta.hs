module LambdaCalculus.Untyped.Beta where

import Data.Functor.Foldable
import Data.Set qualified as S
import LambdaCalculus.Untyped.Alpha (RenameError, safeAlphaRename)
import LambdaCalculus.Untyped.Expr
import LambdaCalculus.Untyped.Vars (Produce (..), fv, isFreeIn, vars)

subst ::
  (Ord a, Produce a) => Expr a -> (a, Expr a) -> Either (RenameError a) (Expr a)
subst expr (toReplace, toSub) = do
  renamePass <- flip cataA expr \case
    VarF a -> pure $ Var a
    AppF expr1 expr2 -> liftA2 App expr1 expr2 -- (P Q)[x := N ] ≡ (P [x := N ])(Q[x := N ])
    AbsF a expr1 -> do
      expr1' <- expr1
      if not (a `isFreeIn` toSub) || not (toReplace `isFreeIn` expr1')
        then pure $ Abs a expr1'
        else do
          let newA = next (fv toSub `S.union` vars expr1')
          newExpr <- safeAlphaRename expr1' (fv expr1') a newA
          pure $ Abs newA newExpr
  pure $ flip cata renamePass \case
    VarF a ->
      if a == toReplace
        then toSub -- x[x := N ] ≡ N
        else Var a -- y[x := N ] ≡ y if x ≡ y
    AppF expr1 expr2 -> App expr1 expr2 -- (P Q)[x := N ] ≡ (P [x := N ])(Q[x := N ])
    AbsF a expr1 -> Abs a expr1
