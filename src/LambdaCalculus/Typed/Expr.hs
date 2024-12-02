{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NoFieldSelectors #-}
module LambdaCalculus.Typed.Expr where

import Data.Functor.Foldable

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

-- Pre-typed λ-terms
data PreTypedF a b f
  = PTVarF a 
  | PTAppF f f
  | PTAbsF (a, b) f

instance Functor (PreTypedF a b) where
  fmap _ (PTVarF a) = PTVarF a
  fmap f (PTAppF e1 e2) = PTAppF (f e1) (f e2)
  fmap f (PTAbsF a e) = PTAbsF a (f e)

data PreTyped a b 
  = PTVar a
  | PTApp (PreTyped a b) (PreTyped a b)
  | PTAbs (a, b) (PreTyped a b)
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

declaration :: a -> Ty b -> Statement a b
declaration tmVar = Statement (PTVar tmVar)

newtype Context a b = Context { ctx :: [Statement a b] }

data Judgement a b = 
  Judgement 
    { context :: Context a b
    , statement :: Statement a b
    }
