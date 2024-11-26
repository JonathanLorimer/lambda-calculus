{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module LambdaCalculus.Expr where

import Control.Monad (void)
import Control.Monad.Reader (runReader, ReaderT (..))
import Control.Monad.Reader.Class (MonadReader (..), asks)
import Control.Monad.State.Strict (MonadState (..), runState, modify, gets, evalStateT)
import Data.DList (DList)
import Data.DList qualified as DL
import Data.DList.Unsafe (DList (..))
import Data.Functor (($>), (<&>))
import Data.Functor.Foldable
import Data.List (delete)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text.Lazy (Text)
import Data.Text.Lazy.Builder qualified as TB
import Data.Validation
import Numeric.Natural (Natural)
import Control.Monad.Except (ExceptT, MonadError (..))
import Control.Monad.Trans.State.Strict (StateT)

{- Core Types -}

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

{- Recursion Schemes -}

type instance Base (Expr a) = ExprF a

instance Recursive (Expr a) where
  project (Var a) = VarF a
  project (Abs a e) = AbsF a e
  project (App e1 e2) = AppF e1 e2

instance Corecursive (Expr a) where
  embed (VarF a) = Var a
  embed (AbsF a e) = Abs a e
  embed (AppF e1 e2) = App e1 e2

{- Subterms -}
sub :: Expr a -> DList (Expr a)
sub = para \case
  VarF a -> DL.singleton $ Var a
  AppF (exprs1, subt1) (exprs2, subt2) ->
    subt1
      <> subt2
      <> DL.singleton (App exprs1 exprs2)
  AbsF a (exprs, subt) -> subt <> DL.singleton (Abs a exprs)

{- Printers -}
printLambda :: (Show a) => Expr a -> Text
printLambda =
  TB.toLazyText . cata \case
    VarF a -> TB.fromString $ show a
    AppF expr1 expr2 ->
      mconcat
        [ TB.singleton '('
        , expr1
        , TB.singleton ')'
        , TB.singleton '('
        , expr2
        , TB.singleton ')'
        ]
    AbsF a expr ->
      mconcat
        [ TB.singleton 'λ'
        , TB.fromString $ show a
        , TB.singleton '.'
        , expr
        ]

printExprTree :: (Show a) => Expr a -> Text
printExprTree =
  TB.toLazyText . flip runReader 0 . cataA \case
    VarF a ->
      ask <&> \indent ->
        mconcat
          [ TB.fromString (replicate indent ' ')
          , TB.fromString "[v] "
          , TB.fromString $ show a
          ]
    AppF expr1 expr2 -> do
      expr1' <- local (+ 2) expr1
      expr2' <- local (+ 2) expr2
      indent <- ask
      pure $
        mconcat
          [ TB.fromString (replicate indent ' ')
          , TB.fromString "[a]"
          , TB.singleton '\n'
          , expr1'
          , TB.singleton '\n'
          , expr2'
          ]
    AbsF a expr -> do
      expr' <- local (+ 2) expr
      indent <- ask
      pure $
        mconcat
          [ TB.fromString (replicate indent ' ')
          , TB.fromString "[λ] "
          , TB.fromString $ show a
          , TB.singleton '.'
          , TB.singleton '\n'
          , expr'
          ]

{- Free Variables -}
fv :: (Eq a, Ord a) => Expr a -> Set a
fv = cata \case
  VarF a -> S.singleton a
  AppF exprs1 exprs2 -> exprs1 <> exprs2
  AbsF a exprs -> S.delete a exprs

isCombinator :: (Eq a, Ord a) => Expr a -> Bool
isCombinator = (==) S.empty . fv

{- Alpha Equivalence -}

data RenameState a = RenameState
  { index :: Natural
  , indexMap :: Map a Natural
  }

emptyRenameState :: RenameState a
emptyRenameState = RenameState 0 M.empty

newtype Ctx n a = Ctx { unCtx :: StateT Natural (ReaderT (Map n Natural) (Either n)) a }
  deriving newtype (Functor, Applicative, Monad, MonadState Natural, MonadReader (Map n Natural), MonadError n)

alphaNormalizeWithVarMap' ::
  forall a. (Ord a) => Expr a -> Ctx a (Expr Natural, Map Natural a)
alphaNormalizeWithVarMap' = cataA \case
  VarF a -> do 
    mIdx <- asks $ M.lookup a
    case mIdx of
      Just idx -> pure (Var idx, M.singleton idx a)
      Nothing -> throwError a
  AppF e1 e2 -> do
    (e1', varMap1) <- e1
    (e2', varMap2) <- e2
    pure (App e1' e2', varMap1 `M.union` varMap2)
  AbsF a e1 -> do
    idx <- get
    modify (+ 1)
    (e1', varMap) <- local (M.alter (const $ Just idx) a) e1
    pure (Abs idx e1', M.insert idx a varMap)

alphaNormalizeWithVarMap :: forall a. (Ord a) => Set a -> Expr a -> Either a (Expr Natural, Map Natural a)
alphaNormalizeWithVarMap freeVariables = 
  fmap (fmap . M.union . M.fromList $ zip [0..] (S.toList freeVariables)) -- insert free variables into varMap
  . flip runReaderT (M.fromList $ zip (S.toList freeVariables) [0..])     -- initialize the index map with free variables
  . flip evalStateT (fromIntegral $ S.size freeVariables)                 -- initialize index counter at the size of the free variable map
  . unCtx
  . alphaNormalizeWithVarMap'

alphaNormalize :: (Ord a) => Set a -> Expr a -> Either a (Expr Natural)
alphaNormalize freeVariables = fmap fst . alphaNormalizeWithVarMap freeVariables

alphaVarMap :: (Ord a) => Set a -> Expr a -> Either a (Map Natural a)
alphaVarMap freeVariables = fmap snd . alphaNormalizeWithVarMap freeVariables

note :: e -> Maybe a -> Validation e a
note e = maybe (Failure e) Success

alphaReconstitute ::
  forall a.
  (Ord a) =>
  Map Natural a ->
  Expr Natural ->
  Validation [Natural] (Expr a)
alphaReconstitute idxMap = cata \case
  VarF idx -> note [idx] $ Var <$> M.lookup idx idxMap
  AppF e1 e2 -> liftA2 App e1 e2
  AbsF idx e -> liftA2 Abs (note [idx] $ M.lookup idx idxMap) e

{- Examples -}
identityE :: Expr String
identityE = Abs "x" $ Var "x"

constE :: Expr String
constE = Abs "x" $ Var "y"
