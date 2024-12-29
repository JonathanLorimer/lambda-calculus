module Shifted.PrimitiveSpec where

import Data.Text (Text)
import Data.Text qualified as T
import Example.Expr (Expr (..), fv)
import Hedgehog (MonadGen, annotateShow, forAll, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Shifted.Primitive (
  LocallyNameless (..),
  Var (..),
  bind,
  close,
  open,
  weaken, rename, substitute,
 )
import Test.Hspec
import Test.Hspec.Hedgehog (
  hedgehog,
  modifyMaxSuccess,
 )
import Control.Applicative (liftA3)
import qualified Data.List.NonEmpty as NE
import qualified Data.Set as S

runs :: Int -> SpecWith a -> SpecWith a
runs = modifyMaxSuccess . const

simpleExample :: Expr Text Text
simpleExample =
  Abs "x" $
    Abs "y" $
      App (Var "x") (Var "y")

spec :: Spec
spec = do
  describe "nameless" $ do
    runs 100 $ it "fromNameless • toNameless" $ hedgehog $ do
      expr <- forAll $ exprG textG
      let nameless = toNameless expr
      annotateShow nameless
      fromNameless nameless === expr

  describe "open" $ do
    it "openₓ λ1.01 ===  λ1. x1" $ do
      let expr :: Expr Text (Var Text)
          expr = Abs "y" $ App (Var $ DeBruijn 0) (Var $ DeBruijn 1)
      shouldBe (open "x" expr) $
        Abs "y" $
          App (Var $ Name "x" 0) (Var $ DeBruijn 0)

    it "openₓ λ1.01 ===  λ1. x1" $ do
      let expr :: Expr Text (Var Text)
          expr = Abs "y" $ App (Var $ DeBruijn 0) (Var $ DeBruijn 1)
      shouldBe (open "x" expr) $
        Abs "y" $
          App (Var $ Name "x" 0) (Var $ DeBruijn 0)

  describe "close" $ do
    it "closeₓ λ1.x1 === λ1.01" $ do
      let expr :: Expr Text (Var Text)
          expr = Abs "y" $ App (Var $ Name "x" 0) (Var $ DeBruijn 0)
      shouldBe (close "x" expr) $
        Abs "y" $
          App (Var $ DeBruijn 0) (Var $ DeBruijn 1)

    it "closeₓ • closeₓ on (x₀ x₁) === λ0.λ1.10" $ do
      let expr :: Expr Text (Var Text)
          expr = App (Var $ Name "x" 0) (Var $ Name "x" 1)
      shouldBe (close "x" $ close "x" expr) $
        App (Var $ DeBruijn 1) (Var $ DeBruijn 0)

    it "closeₓ • closeₓ on (x₁ x₀) === λ0.λ1.01" $ do
      let expr :: Expr Text (Var Text)
          expr = App (Var $ Name "x" 1) (Var $ Name "x" 0)
      shouldBe (close "x" $ close "x" expr) $
        App (Var $ DeBruijn 0) (Var $ DeBruijn 1)

  describe "equations" $ do
    runs 100 $ it "close • open" $ hedgehog $ do
      (name, expr') <- forAll $ liftA2 (,) textG (exprG textG)
      let expr = toNameless expr'
      annotateShow expr
      close name (open name expr) === expr

    runs 100 $ it "open • close" $ hedgehog $ do
      (name, expr') <- forAll $ liftA2 (,) textG (exprG textG)
      let expr = toNameless expr'
      annotateShow expr
      open name (close name expr) === expr

    runs 100 $ it "openₓ • openₓ • closeₓ • closeₓ on (x expr)" $ hedgehog $ do
      (name, expr') <- forAll $ liftA2 (,) textG (exprG textG)
      let expr = toNameless $ App (Var name) expr'
      annotateShow expr
      close name (close name (open name (open name expr))) === expr

    runs 100 $ it "bind • weaken" $ hedgehog $ do
      (name, u', expr') <- forAll $ liftA3 (,,) textG (exprG textG) (exprG textG)
      let expr = toNameless expr'
          u = toNameless u'
      annotateShow expr
      annotateShow u
      bind u (weaken name expr) === expr

    runs 100 $ it "⟨z/y⟩⟨y/x⟩ === ⟨z/x⟩" $ hedgehog $ do
      (x, y, z, expr') <- forAll $ do 
        expr <- exprG textG
        frees <- Gen.mapMaybe (NE.nonEmpty . S.toList . fv) (pure expr)
        y <- textG
        z <- textG
        pure (NE.head frees, y, z, expr)
      let expr = toNameless expr'
      annotateShow expr
      rename z y (rename y x expr) === rename z x expr

    runs 100 $ it "[u/y]⟨y/x⟩ === [u/x]" $ hedgehog $ do
      (x, y, u', expr') <- forAll $ do 
        expr <- exprG textG
        frees <- Gen.mapMaybe (NE.nonEmpty . S.toList . fv) (pure expr)
        u <- exprG textG
        y <- textG
        pure (NE.head frees, y, u, expr)
      let expr = toNameless expr'
          u = toNameless u'
      annotateShow expr
      annotateShow u
      substitute u y (rename y x expr) === substitute u x expr


textG :: (MonadGen m) => m Text
textG = T.pack <$> Gen.string (Range.constant 1 1) Gen.alpha

exprG :: (MonadGen m) => m a -> m (Expr a a)
exprG aG =
  Gen.recursive
    Gen.choice
    [ -- non-recursive generators
      Var <$> aG
    ]
    [ -- recursive generators
      Gen.subtermM (exprG aG) (liftA2 Abs aG . pure)
    , Gen.subterm2 (exprG aG) (exprG aG) App
    ]
