{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NoFieldSelectors #-}

module LambdaCalculus.SimplyTyped.BiDiExpr where

import Control.Monad.Except
import Control.Monad.Reader
import Data.Functor ((<&>))
import Data.Functor.Foldable

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

-- Terms
data ExprF a expr
  = VarF a
  | AbsF expr
  | AppF expr expr

instance Functor (ExprF a) where
  fmap _ (VarF a) = VarF a
  fmap f (AbsF e) = AbsF (f e)
  fmap f (AppF e1 e2) = AppF (f e1) (f e2)

data Expr a
  = Var a
  | Abs (Expr a)
  | App (Expr a) (Expr a)
  deriving (Eq, Ord, Show, Functor, Foldable)

type instance Base (Expr a) = ExprF a

instance Recursive (Expr a) where
  project (Var a) = VarF a
  project (Abs e) = AbsF e
  project (App e1 e2) = AppF e1 e2

instance Corecursive (Expr a) where
  embed (VarF a) = Var a
  embed (AbsF e) = Abs e
  embed (AppF e1 e2) = App e1 e2

-- Checking and Synthesis
data TypeMismatch = TypeMismatch
  { expected :: Tp
  , actual :: Tp
  , term :: Term
  }
  deriving (Eq, Ord, Show)

data UnexpectedType = UnexpectedType
  { expected :: Ty ()
  , actual :: Tp
  , term :: Maybe Term
  }
  deriving (Eq, Ord, Show)

data TypeError
  = TypeMismatchError TypeMismatch
  | UnexpectedTypeError UnexpectedType

type Term = Expr Word
type Tp = Ty Word

newtype Env = Env {env :: [Tp]}

ext :: Tp -> Env -> Env
ext tp initial = Env $ tp : initial.env

newtype Ctx a = Ctx {ctx :: ReaderT Env (Either TypeError) a}
  deriving (Functor, Applicative, Monad, MonadReader Env, MonadError TypeError)
newtype Chk = Chk {chk :: Tp -> Ctx Term}
newtype Syn = Syn {syn :: Ctx (Term, Tp)}

var :: Tp -> Ctx Syn
var tp = asks \bindingEnv ->
  Syn $ asks \useSiteEnv ->
    ( Var . fromIntegral $
        length useSiteEnv.env - (length bindingEnv.env + 1)
    , tp
    )

equate :: Syn -> Chk
equate synTm = Chk \expected -> do
  (term, actual) <- synTm.syn
  if actual == expected
    then pure term
    else
      throwError . TypeMismatchError $
        TypeMismatch
          { expected
          , actual
          , term
          }

abs :: (Syn -> Chk) -> Chk
abs chkBody = Chk \case
  Arrow aType bType -> do
    body <- chkBody <$> var aType
    Abs <$> local (ext aType) (body.chk bType)
  actual ->
    throwError . UnexpectedTypeError $
      UnexpectedType
        { actual
        , expected = Arrow (TyVar ()) (TyVar ())
        , term = Nothing
        }

app :: Syn -> Chk -> Syn
app synFn chkArg = Syn do
  synth <- synFn.syn
  case synth of
    (fn, Arrow aType bType) ->
      chkArg.chk aType <&> \arg ->
        (App fn arg, bType)
    (term, actual) ->
      throwError . UnexpectedTypeError $
        UnexpectedType
          { actual
          , expected = Arrow (TyVar ()) (TyVar ())
          , term = Just term
          }

-- example :: Chk
-- example = lam \xy -> pair (equate (second xy)) (equate (first xy))
