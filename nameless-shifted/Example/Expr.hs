{-# LANGUAGE MultiParamTypeClasses #-}

module Example.Expr where

import Control.Monad.Reader (ask, asks, local, runReader)
import Control.Monad.State.Strict (evalState)
import Data.Bifunctor (Bifunctor (..))
import Data.Foldable
import Data.Functor.Foldable hiding (fold)
import Data.Map.Strict qualified as MS
import Data.Text (Text)
import Shifted.Primitive (Binder (..), LocallyNameless (..), Var (..), Vars (..))

data ExprF b a expr
  = VarF a
  | AbsF b expr
  | AppF expr expr

instance Functor (ExprF b a) where
  fmap _ (VarF a) = VarF a
  fmap f (AbsF b e) = AbsF b (f e)
  fmap f (AppF e1 e2) = AppF (f e1) (f e2)

data Expr b a
  = Var a
  | Abs b (Expr b a)
  | App (Expr b a) (Expr b a)
  deriving (Eq, Ord, Show, Functor, Foldable)

type instance Base (Expr b a) = ExprF b a

instance Recursive (Expr b a) where
  project (Var a) = VarF a
  project (Abs b e) = AbsF b e
  project (App e1 e2) = AppF e1 e2

instance Corecursive (Expr b a) where
  embed (VarF a) = Var a
  embed (AbsF b e) = Abs b e
  embed (AppF e1 e2) = App e1 e2

instance Vars (Expr b) where
  var = Var
  varElim f = cata \case
    VarF a -> f a
    AbsF b expr -> Abs b expr
    AppF expr1 expr2 -> App expr1 expr2

instance Binder Expr Text where
  binder = Abs
  binderElim f = cata \case
    VarF a -> Var a
    AbsF b expr -> f b expr
    AppF expr1 expr2 -> App expr1 expr2

instance LocallyNameless Expr where
  toNameless =
    flip runReader (MS.empty, 0) . cataA \case
      VarF a -> asks $ Var . maybe (Name a 0) DeBruijn . MS.lookup a . fst
      AbsF a expr -> do
        m <- ask
        expr' <- flip local expr $ \(m, idx) ->
          ( MS.alter (const $ Just idx) a m
          , idx + 1
          )
        pure $ Abs a expr'
      AppF expr1 expr2 -> liftA2 App expr1 expr2

  fromNameless =
    flip runReader MS.empty . cataA \case
      VarF a -> case a of
        -- This represents a free variable, so we just use its name
        Name a _ -> pure $ Var a
        -- This is a de-bruijn level so we need to look it up
        DeBruijn w -> asks \m -> case w `MS.lookup` m of
          Just a -> Var a
          Nothing ->
            error $
              fold
                [ "Found binder "
                , show w
                , " but it wasn't present in the environment."
                ]
      AbsF name expr ->
        Abs name
          <$> local (MS.insert 0 name . MS.mapKeysMonotonic (+ 1)) expr
      AppF expr1 expr2 -> liftA2 App expr1 expr2
