{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NoFieldSelectors #-}
module LambdaCalculus.Typed.Expr where

import Data.Functor.Foldable
import qualified Data.List as L
import Control.Monad.Reader (runReader, local, asks)
import Data.Foldable (find)

-- Terms

data ExprF a expr
  = VarF a
  | AbsF a expr
  | AppF expr expr

instance Functor (ExprF a) where
  fmap _ (VarF a) = VarF a
  fmap f (AbsF a e) = AbsF a (f e)
  fmap f (AppF e1 e2) = AppF (f e1) (f e2)

data Expr a
  = Var a
  | Abs a (Expr a)
  | App (Expr a) (Expr a)
  deriving (Eq, Ord, Show, Functor, Foldable)

type instance Base (Expr a) = ExprF a

instance Recursive (Expr a) where
  project (Var a) = VarF a
  project (Abs a e) = AbsF a e
  project (App e1 e2) = AppF e1 e2

instance Corecursive (Expr a) where
  embed (VarF a) = Var a
  embed (AbsF a e) = Abs a e
  embed (AppF e1 e2) = App e1 e2

-- Types

data TyF a f
  = TyVarF a
  | ArrowF f f

instance Functor (TyF a) where
  fmap _ (TyVarF a) = TyVarF a
  fmap f (ArrowF t1 t2) = ArrowF (f t1) (f t2)

data Ty a
  = TyVar a
  | Arrow (Ty a) (Ty a)
  deriving (Eq, Ord, Show, Functor, Foldable)

type instance Base (Ty a) = TyF a

instance Recursive (Ty a) where
  project (TyVar a) = TyVarF a
  project (Arrow t1 t2) = ArrowF t1 t2

instance Corecursive (Ty a) where
  embed (TyVarF a) = TyVar a
  embed (ArrowF t1 t2) = Arrow t1 t2

printType :: (Show a) => Ty a -> String
printType = cata \case
  TyVarF a -> show a
  ArrowF t1 t2 -> "(" <> t1 <> " -> " <> t2 <> ")"


-- Pre-typed λ-terms
data PreTypedF a b f
  = PTVarF a 
  | PTAppF f f
  | PTAbsF (a, Ty b) f

instance Functor (PreTypedF a b) where
  fmap _ (PTVarF a) = PTVarF a
  fmap f (PTAppF e1 e2) = PTAppF (f e1) (f e2)
  fmap f (PTAbsF a e) = PTAbsF a (f e)

data PreTyped a b 
  = PTVar a
  | PTApp (PreTyped a b) (PreTyped a b)
  | PTAbs (a, Ty b) (PreTyped a b)
  deriving (Eq, Ord, Show, Functor, Foldable)

type instance Base (PreTyped a b) = PreTypedF a b

instance Recursive (PreTyped a b) where
  project (PTVar a) = PTVarF a
  project (PTApp e1 e2) = PTAppF e1 e2
  project (PTAbs ab e) = PTAbsF ab e

instance Corecursive (PreTyped a b) where
  embed (PTVarF a) = PTVar a
  embed (PTAppF e1 e2) = PTApp e1 e2
  embed (PTAbsF ab e) = PTAbs ab e

data Statement a b = Statement (PreTyped a b) (Ty b)
  deriving (Eq, Ord, Show)

data Declaration a b = Declaration 
  { subject :: a 
  , ty :: Ty b
  }
  deriving (Eq, Ord, Show)

newtype Context a b = Context { ctx :: [Declaration a b] }
  deriving (Eq, Ord, Show)

emptyCtx :: Context a b
emptyCtx = Context []

ext :: Declaration a b -> Context a b -> Context a b
ext decl context = Context $ decl : context.ctx

data Judgement a b = 
  Judgement 
    { context :: Context a b
    , statement :: Statement a b
    }

wellTyped :: (Eq a, Eq b, Show a, Show b) => PreTyped a b -> Ty b
wellTyped = flip runReader emptyCtx . cataA \case
  PTVarF tmVar -> asks \context ->
    case find (\d -> d.subject == tmVar) context.ctx of
      Nothing -> error $ "Couldn't find " <> show tmVar <> " in context: " <> show context.ctx
      Just decl -> decl.ty
  PTAppF appTy1' appTy2' -> do
    appTy1 <- appTy1'
    appTy2 <- appTy2'
    case appTy1 of
      TyVar a -> error $ "Expected function type but got type var " <> show a
      Arrow aty bty | aty == appTy2 -> pure bty
      Arrow aty _ -> error $ "Input type to arrow " <> show aty <> " does not match type of the expression it was applied to " <> show appTy2
  PTAbsF (tmVar, tp) bodyTy' -> do
    bodyTy <- local (ext $ Declaration tmVar tp) bodyTy'
    pure $ Arrow tp bodyTy

example :: PreTyped Char Char 
example = PTAbs ('y', Arrow (TyVar 'a') (TyVar 'b'))
  $ PTAbs ('z', TyVar 'b')
    $ PTApp (PTVar 'y') (PTVar 'z')
