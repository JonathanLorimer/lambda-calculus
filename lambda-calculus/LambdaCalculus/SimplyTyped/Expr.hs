{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NoFieldSelectors #-}

module LambdaCalculus.SimplyTyped.Expr where

import Control.Monad.Reader (ask, asks, local, runReader)
import Data.Bifunctor (bimap)
import Data.Foldable (find, fold)
import Data.Functor.Foldable hiding (fold)
import Data.List qualified as L
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
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
import Text.Show.Unicode (ushow)
import qualified Shifted.Operation.Index as OI

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
  deriving (Eq, Ord, Functor, Foldable)

(|->) :: Ty a -> Ty a -> Ty a
(|->) = Arrow

infixr 6 |->

instance (Show a) => Show (Ty a) where
  showsPrec p (TyVar a) = showsPrec p a
  showsPrec p (Arrow t1 t2) =
    showParen (p > 0) $
      showsPrec 1 t1
        . showString " -> "
        . shows t2

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
data PreTypedF ty name var f
  = PTVarF var
  | PTAppF f f
  | PTAbsF name (Ty ty) f
  deriving (Eq, Ord, Show, Functor, Foldable)

data PreTyped ty name var
  = PTVar var
  | PTApp (PreTyped ty name var) (PreTyped ty name var)
  | PTAbs name (Ty ty) (PreTyped ty name var)
  deriving (Eq, Ord, Show, Functor, Foldable)

type instance Base (PreTyped ty name var) = PreTypedF ty name var

instance Recursive (PreTyped ty name var) where
  project (PTVar var) = PTVarF var
  project (PTApp e1 e2) = PTAppF e1 e2
  project (PTAbs name ty e) = PTAbsF name ty e

instance Corecursive (PreTyped ty name var) where
  embed (PTVarF var) = PTVar var
  embed (PTAppF e1 e2) = PTApp e1 e2
  embed (PTAbsF name ty e) = PTAbs name ty e

-- Shifted instances
instance Vars (PreTyped ty name) where
  var = PTVar
  sub f =
    flip runReader 0 . cataA \case
      PTVarF a -> asks $ f a
      PTAbsF b ty expr -> PTAbs b ty <$> local (+ 1) expr
      PTAppF expr1 expr2 -> liftA2 PTApp expr1 expr2

instance Indexed (PreTyped ty name) where
  maxIdx = cata \case
    PTVarF a -> Nothing
    PTAbsF _ _ expr -> Just $ maybe 0 (+ 1) expr
    PTAppF expr1 expr2 -> fmap getMax $ (Max <$> expr1) <> (Max <$> expr2)

  mapFreeIndices f = 
    flip runReader 0 . cata \case
      PTVarF (DeBruijn n) -> asks \maxLevel ->
        PTVar . DeBruijn $
          if n > maxLevel
            then f n
            else n
      PTVarF a -> pure $ PTVar a
      PTAbsF name ty expr -> PTAbs name ty <$> local (+ 1) expr
      PTAppF expr1 expr2 -> liftA2 PTApp expr1 expr2

instance Levelled (PreTyped ty b) where
  mapBoundLevels f =
    flip runReader 0 . cata \case
      PTVarF (DeBruijn n) -> asks \maxLevel ->
        PTVar . DeBruijn $
          if n > maxLevel
            then n
            else f n
      PTVarF a -> pure $ PTVar a
      PTAbsF name ty expr -> PTAbs name ty <$> local (+ 1) expr
      PTAppF expr1 expr2 -> liftA2 PTApp expr1 expr2

-- Locally nameless instances
instance LocallyNameless Level (PreTyped ty) where
  toNameless =
    flip runReader (MS.empty, 0) . cataA \case
      PTVarF a -> asks $ PTVar . maybe (Free a 0) DeBruijn . MS.lookup a . fst
      PTAbsF a ty expr -> do
        m <- ask
        expr' <- flip local expr $ \(m, idx) ->
          ( MS.alter (const $ Just idx) a m
          , idx + 1
          )
        pure $ PTAbs a ty expr'
      PTAppF expr1 expr2 -> liftA2 PTApp expr1 expr2

  fromNameless =
    flip runReader MS.empty . cataA \case
      PTVarF a -> case a of
        -- This represents a free variable, so we just use its name
        Free a _ -> pure $ PTVar a
        -- This is a de-bruijn level so we need to look it up
        DeBruijn w -> asks \m -> case w `MS.lookup` m of
          Just a -> PTVar a
          Nothing ->
            error $
              fold
                [ "Found bound variable "
                , show w
                , " but it wasn't present in the environment."
                ]
      PTAbsF name ty expr ->
        fmap (PTAbs name ty) . flip local expr $ \m ->
          case MS.lookupMax m of
            Nothing -> MS.insert 0 name m
            Just (w, _) -> MS.insert (w + 1) name m
      PTAppF expr1 expr2 -> liftA2 PTApp expr1 expr2

instance LocallyNameless Index (PreTyped ty) where
  toNameless =
    flip runReader MS.empty . cataA \case
      PTVarF a -> asks $ PTVar . maybe (Free a 0) DeBruijn . MS.lookup a
      PTAbsF name ty expr ->
        fmap (PTAbs name ty) . local (MS.alter (const $ Just 0) name . fmap (+ 1)) $
          expr
      PTAppF expr1 expr2 -> liftA2 PTApp expr1 expr2

  fromNameless =
    flip runReader MS.empty . cataA \case
      PTVarF a -> case a of
        -- This represents a free variable, so we just use its name
        Free a _ -> pure $ PTVar a
        -- This is a de-bruijn level so we need to look it up
        DeBruijn w -> asks \m -> case w `MS.lookup` m of
          Just a -> PTVar a
          Nothing ->
            error $
              fold
                [ "Found bound variable "
                , show w
                , " but it wasn't present in the environment."
                ]
      PTAbsF name ty expr ->
        fmap (PTAbs name ty)
          . local (MS.alter (const $ Just name) 0 . MS.mapKeysMonotonic (+ 1))
          $ expr
      PTAppF expr1 expr2 -> liftA2 PTApp expr1 expr2

fvNL :: (Ord a) => PreTyped ty b (Var d a) -> Set a
fvNL = cata \case
  PTVarF (Free a _) -> S.singleton a
  PTVarF (DeBruijn _) -> S.empty
  PTAppF exprs1 exprs2 -> exprs1 <> exprs2
  PTAbsF a ty exprs -> exprs

fv :: (Ord a) => PreTyped ty a a -> Set a
fv = cata \case
  PTVarF a -> S.singleton a
  PTAppF exprs1 exprs2 -> exprs1 <> exprs2
  PTAbsF a ty exprs -> S.delete a exprs

isNF :: PreTyped ty a b -> Bool
isNF =
  getAll . para \case
    PTVarF _ -> All True
    PTAppF (PTAbs{}, _) (_, _) -> All False
    PTAppF (_, a1) (_, a2) -> a1 <> a2
    PTAbsF _ _ (_, a1) -> a1

whnfLvl :: PreTyped ty Text (Var Level Text) -> PreTyped ty Text (Var Level Text)
whnfLvl = \case
  -- NOTE: There is an optimization where we accumulate the list of
  -- arguments create by successive `App`, this allows us to take
  -- advantage of tail call optimization
  PTApp f u -> case whnfLvl f of
    PTAbs name _ body -> whnfLvl . OL.substitute' 0 u name . OL.open name $ body
    expr -> PTApp expr u
  -- NOTE: Below is the primary distinction between nf and whnf
  expr -> expr

whnfIdx :: PreTyped ty Text (Var Index Text) -> PreTyped ty Text (Var Index Text)
whnfIdx = \case
  -- NOTE: There is an optimization where we accumulate the list of
  -- arguments create by successive `App`, this allows us to take
  -- advantage of tail call optimization
  PTApp f u -> 
    case whnfIdx f of
      PTAbs name ty body -> 
        whnfIdx . OI.substitute' 0 u name . OI.open name $ body
      expr -> PTApp expr u
  -- NOTE: Below is the primary distinction between nf and whnfLvl
  expr -> expr


nfLvl :: PreTyped ty Text (Var Level Text) -> PreTyped ty Text (Var Level Text)
nfLvl = \case
  -- NOTE: There is an optimization where we accumulate the list of
  -- arguments create by successive `App`, this allows us to take
  -- advantage of tail call optimization
  PTApp f u -> case nfLvl f of
    PTAbs name _ body -> nfLvl . OL.substitute' 0 u name . OL.open name $ body
    expr -> PTApp expr u
  -- NOTE: Below is the primary distinction between nf and whnf
  PTAbs name ty body -> PTAbs name ty . OL.close name . nfLvl . OL.open name $ body
  PTVar a -> PTVar a

nfIdx :: PreTyped ty Text (Var Index Text) -> PreTyped ty Text (Var Index Text)
nfIdx = \case
  -- NOTE: There is an optimization where we accumulate the list of
  -- arguments create by successive `App`, this allows us to take
  -- advantage of tail call optimization
  PTApp f u -> case nfIdx f of
    PTAbs name ty body ->
      nfIdx
        . OI.substitute' 0 u name
        . OI.open name
        $ body
    expr -> PTApp expr u
  -- NOTE: Below is the primary distinction between nfLvl and whnfLvl
  PTAbs name ty body ->
    PTAbs name ty
      . OI.close name
      . nfIdx
      . OI.open name
      $ body
  PTVar a -> PTVar a

step :: PreTyped ty Text (Var Level Text) -> PreTyped ty Text (Var Level Text)
step = \case
  PTApp f u -> case f of
    PTAbs name _ body -> OL.substitute u name body
    expr -> PTApp (nfLvl expr) u
  PTAbs name ty body -> PTAbs name ty (nfLvl body)
  PTVar a -> PTVar a

wellTyped
  :: (Ord a, Eq ty, Show a, Show ty) => MS.Map a (Ty ty) -> PreTyped ty a a -> Ty ty
wellTyped gamma =
  flip runReader gamma . cataA \case
    PTVarF tmVar -> asks \ctx ->
      case MS.lookup tmVar ctx of
        Nothing ->
          error $ "Couldn't find " <> show tmVar <> " in context: " <> show ctx
        Just ty -> ty
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
      bodyTy <- local (MS.alter (const $ Just tp) tmVar) bodyTy'
      pure $ Arrow tp bodyTy

typeCheck
  :: (Ord a, Eq ty, Show a, Show ty)
  => MS.Map a (Ty ty)
  -> PreTyped ty a a
  -> Ty ty
  -> Bool
typeCheck initialCtx term expectedTy = (==) expectedTy $ wellTyped initialCtx term

_const :: Ty ty -> Ty ty -> PreTyped ty Text Text
_const t1 t2 = PTAbs "x" t1 $ PTAbs "y" t2 $ PTVar "x"

_id :: Ty ty -> PreTyped ty Text Text
_id t1 = PTAbs "x" t1 $ PTVar "x"

_ap :: Ty ty -> Ty ty -> PreTyped ty Text Text
_ap t1 t2 = PTAbs "f" t1 $ PTAbs "y" t2 $ PTApp (PTVar "f") (PTVar "y")
