{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module LambdaCalculus.Untyped.Expr where

import Control.Monad.Reader (ask, asks, local, runReader)
import Control.Monad.State.Strict (evalState, gets)
import Data.Bifunctor (Bifunctor (..))
import Data.Foldable
import Data.Functor.Foldable hiding (fold)
import Data.Map.Strict qualified as MS
import Data.Monoid (All (..))
import Data.Semigroup (Max (..))
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text (Text)
import Debug.Trace qualified as Debug
import Shifted.Nameless
import Shifted.Operation.Level qualified as OL
import Shifted.Var

data ExprF b a f
  = VarF a
  | AbsF b f
  | AppF f f
  deriving (Eq, Ord, Show, Functor, Foldable)

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
  sub f =
    flip runReader 0 . cataA \case
      VarF a -> asks $ f a
      AbsF b expr -> Abs b <$> local (+ 1) expr
      AppF expr1 expr2 -> liftA2 App expr1 expr2

instance LocallyNameless Level Expr where
  toNameless =
    flip runReader (MS.empty, 0) . cataA \case
      VarF a -> asks $ Var . maybe (Free a 0) DeBruijn . MS.lookup a . fst
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
        Free a _ -> pure $ Var a
        -- This is a de-bruijn level so we need to look it up
        DeBruijn w -> asks \m -> case w `MS.lookup` m of
          Just a -> Var a
          Nothing ->
            error $
              fold
                [ "Found bound variable "
                , show w
                , " but it wasn't present in the environment."
                ]
      AbsF name expr ->
        fmap (Abs name) . flip local expr $ \m ->
          case MS.lookupMax m of
            Nothing -> MS.insert 0 name m
            Just (w, _) -> MS.insert (w + 1) name m
      AppF expr1 expr2 -> liftA2 App expr1 expr2

instance LocallyNameless Index Expr where
  toNameless =
    flip runReader MS.empty . cataA \case
      VarF a -> asks $ Var . maybe (Free a 0) DeBruijn . MS.lookup a
      AbsF name expr ->
        fmap (Abs name) . local (MS.alter (const $ Just 0) name . fmap (+ 1)) $ expr
      AppF expr1 expr2 -> liftA2 App expr1 expr2

  fromNameless =
    flip runReader MS.empty . cataA \case
      VarF a -> case a of
        -- This represents a free variable, so we just use its name
        Free a _ -> pure $ Var a
        -- This is a de-bruijn level so we need to look it up
        DeBruijn w -> asks \m -> case w `MS.lookup` m of
          Just a -> Var a
          Nothing ->
            error $
              fold
                [ "Found bound variable "
                , show w
                , " but it wasn't present in the environment."
                ]
      AbsF name expr ->
        fmap (Abs name)
          . local (MS.alter (const $ Just name) 0 . MS.mapKeysMonotonic (+ 1))
          $ expr
      AppF expr1 expr2 -> liftA2 App expr1 expr2

instance Indexed (Expr b) where
  maxIdx = cata \case
    VarF a -> Nothing
    AbsF _ expr -> Just $ maybe 0 (+ 1) expr
    AppF expr1 expr2 -> fmap getMax $ (Max <$> expr1) <> (Max <$> expr2)

instance Levelled (Expr b) where
  mapBoundLevels f =
    flip runReader 0 . cata \case
      VarF (DeBruijn n) -> asks \maxLevel ->
        Var . DeBruijn $
          if n > maxLevel
            then n
            else f n
      VarF a -> pure $ Var a
      AbsF name expr -> Abs name <$> local (+ 1) expr
      AppF expr1 expr2 -> liftA2 App expr1 expr2

fv :: (Eq a, Ord a) => Expr a a -> Set a
fv = cata \case
  VarF a -> S.singleton a
  AppF exprs1 exprs2 -> exprs1 <> exprs2
  AbsF a exprs -> S.delete a exprs

isNF :: Expr a b -> Bool
isNF =
  getAll . para \case
    VarF _ -> All True
    AppF (Abs _ _, _) (_, _) -> All False
    AppF (_, a1) (_, a2) -> a1 <> a2
    AbsF _ (_, a1) -> a1

whnfLvl :: Expr Text (Var Level Text) -> Expr Text (Var Level Text)
whnfLvl = \case
  -- NOTE: There is an optimization where we accumulate the list of
  -- arguments create by successive `App`, this allows us to take
  -- advantage of tail call optimization
  App f u -> case whnfLvl f of
    Abs name body ->
      whnfLvl
        . OL.substitute' 0 u name
        . OL.open name
        $ body
    expr -> App expr u
  -- NOTE: Below is the primary distinction between nf and whnfLvl
  expr -> expr

nfLvl :: Expr Text (Var Level Text) -> Expr Text (Var Level Text)
nfLvl = \case
  -- NOTE: There is an optimization where we accumulate the list of
  -- arguments create by successive `App`, this allows us to take
  -- advantage of tail call optimization
  App f u -> case nfLvl f of
    Abs name body ->
      nfLvl
        . OL.substitute' 0 u name
        . OL.open name
        $ body
    expr -> App expr u
  -- NOTE: Below is the primary distinction between nfLvl and whnfLvl
  Abs name body ->
    Abs name
      . OL.close name
      . nfLvl
      . OL.open name
      $ body
  Var a -> Var a

_const :: Expr Text Text
_const = Abs "a" $ Abs "b" $ Var "a"

_id :: Expr Text Text
_id = Abs "x" $ Var "x"

_ap :: Expr Text Text
_ap = Abs "f" $ Abs "y" $ App (Var "f") (Var "y")
