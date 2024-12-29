module LambdaCalculus.Untyped.Vars where

import Data.Foldable (find)
import Data.Functor.Foldable
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text qualified as TS
import Data.Text.Lazy qualified as TL
import LambdaCalculus.Untyped.Expr
import Numeric.Natural

fv :: (Eq a, Ord a) => Expr a -> Set a
fv = cata \case
  VarF a -> S.singleton a
  AppF exprs1 exprs2 -> exprs1 <> exprs2
  AbsF a exprs -> S.delete a exprs

binders :: (Eq a, Ord a) => Expr a -> Set a
binders = cata \case
  VarF a -> S.empty
  AppF exprs1 exprs2 -> exprs1 <> exprs2
  AbsF a exprs -> S.insert a exprs

vars :: (Eq a, Ord a) => Expr a -> Set a
vars = cata \case
  VarF a -> S.singleton a
  AppF exprs1 exprs2 -> exprs1 <> exprs2
  AbsF a exprs -> S.insert a exprs

isCombinator :: (Eq a, Ord a) => Expr a -> Bool
isCombinator = (==) S.empty . fv

isFreeIn :: (Ord a) => a -> Expr a -> Bool
isFreeIn a = S.member a . fv

class Produce a where
  next :: Set a -> a

instance Produce TL.Text where
  next s = case find (not . flip S.member s) $ TL.pack . show <$> [0 ..] of
    Nothing -> error "Produce.next for Lazy Text failed"
    Just a -> a

instance Produce TS.Text where
  next s = case find (not . flip S.member s) $ TS.pack . show <$> [0 ..] of
    Nothing -> error "Produce.next for Strict Text failed"
    Just a -> a

instance Produce Natural where
  next s = case find (not . flip S.member s) [0 ..] of
    Nothing -> error "Produce.next for Natural failed"
    Just a -> a
