module LambdaCalculus.Untyped.Alpha where

import Control.Monad.Except (MonadError (..))
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Bifunctor
import Data.Functor.Foldable
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Set (Set)
import Data.Set qualified as S
import Data.Validation (Validation, toEither)
import LambdaCalculus.Lib.Validation (note)
import LambdaCalculus.Untyped.Expr
import LambdaCalculus.Untyped.Vars (fv, vars)
import Numeric.Natural
import Control.Monad (when)

newtype Ctx n a = Ctx {unCtx :: StateT Natural (ReaderT (Map n Natural) (Either n)) a}
  deriving newtype
    ( Functor
    , Applicative
    , Monad
    , MonadState Natural
    , MonadReader (Map n Natural)
    , MonadError n
    )

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

alphaNormalizeWithVarMap ::
  forall a. (Ord a) => Set a -> Expr a -> Either a (Expr Natural, Map Natural a)
alphaNormalizeWithVarMap freeVariables =
  fmap (fmap . M.union . M.fromList $ zip [0 ..] (S.toList freeVariables)) -- insert free variables into varMap
    . flip runReaderT (M.fromList $ zip (S.toList freeVariables) [0 ..]) -- initialize the index map with free variables
    . flip evalStateT (fromIntegral $ S.size freeVariables) -- initialize index counter at the size of the free variable map
    . unCtx
    . alphaNormalizeWithVarMap'

alphaNormalize :: (Ord a) => Set a -> Expr a -> Either a (Expr Natural)
alphaNormalize freeVariables = fmap fst . alphaNormalizeWithVarMap freeVariables

alphaVarMap :: (Ord a) => Set a -> Expr a -> Either a (Map Natural a)
alphaVarMap freeVariables = fmap snd . alphaNormalizeWithVarMap freeVariables

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

data RenameError a
  = NormalizationError a
  | ReconstitutionError [Natural]
  | BadRenaming (Expr a) a
  deriving (Eq, Ord, Show)

alphaRename ::
  (Ord a) => Expr a -> Set a -> a -> a -> Either (RenameError a) (Expr a)
alphaRename expr freeVars old new = do
  (exprN, varMap) <-
    first NormalizationError $ alphaNormalizeWithVarMap freeVars expr
  let free = fv exprN
      toRename = M.filter (== old) varMap
      freeToRename = M.restrictKeys toRename free
      newSubMap = new <$ freeToRename
      newFullMap = newSubMap `M.union` varMap -- Depends on union being left biased
  first ReconstitutionError . toEither $ alphaReconstitute newFullMap exprN

safeAlphaRename ::
  (Ord a) => Expr a -> Set a -> a -> a -> Either (RenameError a) (Expr a)
safeAlphaRename expr freeVars old new = do
  when (S.member new $ vars expr) $
    throwError $
      BadRenaming expr new
  alphaRename expr freeVars old new
