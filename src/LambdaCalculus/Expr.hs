{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module LambdaCalculus.Expr where

import Control.Monad.Reader (runReader)
import Control.Monad.Reader.Class (MonadReader (..))
import Control.Monad.State.Strict (MonadState (..), runState)
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
import Numeric.Natural (Natural)

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
  deriving (Eq, Ord, Show, Functor)

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

data RenameState a = RenameState
  { index :: Natural
  , indexMap :: Map a Natural
  }

emptyRenameState :: RenameState a
emptyRenameState = RenameState 0 M.empty

alphaNormalizeWithVarMap :: forall a. (Ord a) => Expr a -> (Expr Natural, Map Natural a)
alphaNormalizeWithVarMap =
  fst . flip runState (emptyRenameState @a) . cataA \case
    VarF a -> state \rs ->
      ( (Var rs.index, M.singleton rs.index a)
      , RenameState
          { index = rs.index + 1
          , indexMap = M.insert a rs.index rs.indexMap
          }
      )
    AppF e1 e2 -> do 
      (e1', varMap1) <- e1
      (e2', varMap2) <- e2
      pure (App e1' e2', varMap1 `M.union` varMap2)
    AbsF a e1 -> do
      -- NOTE: It is very important to get the downstream state computation
      -- first so that we can find the bound variable indices in the map
      (e1', varMap) <- e1
      rs <- get
      case M.lookup a rs.indexMap of
        Just idx -> 
          -- Leave varMap unchanged, since we already inserted at the 
          -- bound variable site
          (Abs idx e1', varMap)
            <$ put
              (rs {
                indexMap = M.delete a rs.indexMap
              }
              )
        Nothing ->
          (Abs rs.index e1', M.insert rs.index a varMap)
            <$ put
              ( rs
                  { index = rs.index + 1
                  , indexMap = M.insert a rs.index rs.indexMap
                  }
              )

alphaNormalize :: (Ord a) => Expr a -> Expr Natural
alphaNormalize = fst . alphaNormalizeWithVarMap

alphaVarMap :: (Ord a) => Expr a -> Map Natural a
alphaVarMap = snd . alphaNormalizeWithVarMap

{- Examples -}
identityE :: Expr String
identityE = Abs "x" $ Var "x"

constE :: Expr String
constE = Abs "x" $ Var "y"
