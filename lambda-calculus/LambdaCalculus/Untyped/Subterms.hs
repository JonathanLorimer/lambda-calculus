module LambdaCalculus.Untyped.Subterms where

import Data.DList (DList)
import Data.DList qualified as DL
import Data.Functor.Foldable
import LambdaCalculus.Untyped.Expr

sub :: Expr a b -> DList (Expr a b)
sub = para \case
  VarF a -> DL.singleton $ Var a
  AppF (exprs1, subt1) (exprs2, subt2) ->
    subt1
      <> subt2
      <> DL.singleton (App exprs1 exprs2)
  AbsF a (exprs, subt) -> subt <> DL.singleton (Abs a exprs)
