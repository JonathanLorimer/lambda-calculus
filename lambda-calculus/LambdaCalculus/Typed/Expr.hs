{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NoFieldSelectors #-}

module LambdaCalculus.Typed.Expr where

import Control.Monad.Reader (asks, local, runReader)
import Data.Bifunctor (bimap)
import Data.Foldable (find)
import Data.Functor.Foldable
import Data.List qualified as L
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M

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
  | PTAbsF a (Ty b) f

instance Functor (PreTypedF a b) where
  fmap _ (PTVarF a) = PTVarF a
  fmap f (PTAppF e1 e2) = PTAppF (f e1) (f e2)
  fmap f (PTAbsF a b e) = PTAbsF a b (f e)

data PreTyped a b
  = PTVar a
  | PTApp (PreTyped a b) (PreTyped a b)
  | PTAbs a (Ty b) (PreTyped a b)
  deriving (Eq, Ord, Show, Functor, Foldable)

type instance Base (PreTyped a b) = PreTypedF a b

instance Recursive (PreTyped a b) where
  project (PTVar a) = PTVarF a
  project (PTApp e1 e2) = PTAppF e1 e2
  project (PTAbs a b e) = PTAbsF a b e

instance Corecursive (PreTyped a b) where
  embed (PTVarF a) = PTVar a
  embed (PTAppF e1 e2) = PTApp e1 e2
  embed (PTAbsF a b e) = PTAbs a b e

data Statement a b = Statement (PreTyped a b) (Ty b)
  deriving (Eq, Ord, Show)

data Declaration a b = Declaration
  { subject :: a
  , ty :: Ty b
  }
  deriving (Eq, Ord, Show)

newtype Context a b = Context {ctx :: [Declaration a b]}
  deriving (Eq, Ord, Show)

emptyCtx :: Context a b
emptyCtx = Context []

ext :: Declaration a b -> Context a b -> Context a b
ext decl context = Context $ decl : context.ctx

data Judgement a b = Judgement
  { context :: Context a b
  , statement :: Statement a b
  }

wellTyped :: (Eq a, Eq b, Show a, Show b) => Context a b -> PreTyped a b -> Ty b
wellTyped initalCtx =
  flip runReader initalCtx . cataA \case
    PTVarF tmVar -> asks \context ->
      case find (\d -> d.subject == tmVar) context.ctx of
        Nothing ->
          error $ "Couldn't find " <> show tmVar <> " in context: " <> show context.ctx
        Just decl -> decl.ty
    PTAppF appTy1' appTy2' -> do
      appTy1 <- appTy1'
      appTy2 <- appTy2'
      case appTy1 of
        TyVar a -> error $ "Expected function type but got type var " <> show a
        Arrow aty bty | aty == appTy2 -> pure bty
        Arrow aty _ ->
          error $
            "Input type to arrow "
              <> show aty
              <> " does not match type of the expression it was applied to "
              <> show appTy2
    PTAbsF tmVar tp bodyTy' -> do
      bodyTy <- local (ext $ Declaration tmVar tp) bodyTy'
      pure $ Arrow tp bodyTy

closedWellTyped :: (Eq a, Eq b, Show a, Show b) => PreTyped a b -> Ty b
closedWellTyped = wellTyped emptyCtx

example1 :: PreTyped Char Char
example1 =
  PTAbs 'y' (Arrow (TyVar 'a') (TyVar 'b')) $
    PTAbs 'z' (TyVar 'a') $
      PTApp (PTVar 'y') (PTVar 'z')

wellTypedExample :: String
wellTypedExample = printType . closedWellTyped $ example1

typeCheck ::
  (Eq a, Eq b, Show a, Show b) => Context a b -> PreTyped a b -> Ty b -> Bool
typeCheck initialCtx term expectedTy = (==) expectedTy $ wellTyped initialCtx term

-- x : α → α, y : (α → α) → β ⊢ (λz : β . λu : γ . z)(y x) : γ → β .
typeCheckExample :: Bool
typeCheckExample =
  let
    ctx =
      Context
        [ Declaration 'x' (Arrow (TyVar 'a') (TyVar 'a'))
        , Declaration 'y' (Arrow (Arrow (TyVar 'a') (TyVar 'a')) (TyVar 'b'))
        ]
    term =
      PTApp
        (PTAbs 'z' (TyVar 'b') $ PTAbs 'u' (TyVar 'y') $ PTVar 'z')
        (PTApp (PTVar 'y') (PTVar 'x'))
    ty = Arrow (TyVar 'y') (TyVar 'b')
   in
    typeCheck ctx term ty

domain :: Context a b -> [a]
domain (Context ctx) = fmap (\decl -> decl.subject) ctx

exampleContext0 :: Context String String
exampleContext0 =
  Context
    [ Declaration "y" (TyVar "sigma")
    , Declaration "x1" (TyVar "rho1")
    , Declaration "x2" (TyVar "rho2")
    , Declaration "z" (TyVar "tau")
    , Declaration "x3" (TyVar "rho3")
    ]

domEx1 :: [a]
domEx1 = domain emptyCtx

-- $> import LambdaCalculus.Typed.Expr

-- $> domEx1 == []

-- $> domain exampleContext0 == ["y", "x1", "x2", "z", "x3"]

subcontext :: forall a b. (Eq a, Eq b) => Context a b -> Context a b -> Bool
subcontext (Context ctx') (Context ctx) = null $ go ctx' ctx
 where
  go :: [Declaration a b] -> [Declaration a b] -> [Declaration a b]
  go xs [] = xs
  go [] xs = []
  go (x : xs) (y : ys) = go (if x == y then xs else x : xs) ys

exampleContext1 :: Context String String
exampleContext1 =
  Context
    [ Declaration "x1" (TyVar "rho1")
    , Declaration "z" (TyVar "tau")
    ]

-- $> emptyCtx `subcontext` exampleContext1

-- $> exampleContext1 `subcontext` exampleContext0

permutation :: forall a b. (Ord a, Ord b) => Context a b -> Context a b -> Bool
permutation ctx1 ctx2 = uncurry (==) $ bimap toCountMap toCountMap (ctx1, ctx2)

toCountMap :: (Ord a, Ord b) => Context a b -> Map (Declaration a b) Word
toCountMap =
  foldr (M.alter \case Just n -> Just $ n + 1; Nothing -> Just 1) M.empty . (.ctx)

exampleContext2 :: Context String String
exampleContext2 =
  Context
    [ Declaration "x2" (TyVar "rho2")
    , Declaration "x1" (TyVar "rho1")
    , Declaration "z" (TyVar "tau")
    , Declaration "x3" (TyVar "rho3")
    , Declaration "y" (TyVar "sigma")
    ]

-- $> exampleContext2 `permutation` exampleContext0

projection :: (Eq a) => [Declaration a b] -> [a] -> [Declaration a b]
projection gamma phi = filter (\decl -> decl.subject `elem` phi) gamma

expectedContext :: Context String String
expectedContext =
  Context
    [ Declaration "x1" (TyVar "rho1")
    , Declaration "z" (TyVar "tau")
    ]

-- $> exampleContext0.ctx `projection` ["z", "u", "x1"] == expectedContext.ctx
