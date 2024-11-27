{-# LANGUAGE LambdaCase #-}
module LambdaCalculus.ExprSpec where

import Data.Validation (Validation (..))
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import LambdaCalculus.Expr
    ( Expr(..),
      alphaNormalizeWithVarMap,
      alphaReconstitute,
      printExprTree,
      fv, alphaRename, vars, safeAlphaRename )
import Test.Hspec
import Test.Hspec.Hedgehog (MonadGen, forAll, hedgehog, (===), PropertyT, annotate, annotateShow, failure, (/==), modifyMaxDiscardRatio)
import Data.Foldable (Foldable (..))
import Data.List (intersperse)
import qualified Data.Map.Strict as M
import qualified Data.Text.Lazy as TL
import Test.Hspec.QuickCheck (modifyMaxSuccess)
import qualified Data.Set as S
import Test.HUnit (assertFailure)
import qualified Data.List.NonEmpty as NE

assertRight :: (Show e) => Either e v -> IO v
assertRight = \case
  Left e -> assertFailure $ "Expected Right but got Left " <> show e
  Right v -> pure v

assertJust :: Maybe a -> IO a
assertJust = \case
  Nothing -> assertFailure "Expected Just but got Nothing"
  Just a -> pure a

assertRightProp :: (Show e) => Either e v -> PropertyT IO v
assertRightProp = \case
  Left e -> do
    annotate "unexpected Left:"
    annotateShow e
    failure
  Right v -> pure v

spec :: Spec
spec =
  describe "alpha renaming" $ do
    describe "alphaRename" $ do
      modifyMaxDiscardRatio (const 1000) . modifyMaxSuccess (const 10000) $
        it "should round trip" $
          hedgehog $ do
            (expr, old, new) <- forAll $ do 
              let strG = Gen.string (Range.linear 0 50) Gen.alpha
              expr <- exprG strG
              frees <- Gen.mapMaybe (NE.nonEmpty . S.toList . fv) (pure expr)
              -- NOTE: we enforce the "safety" invariant for renaming here
              new <- Gen.filter (not . flip S.member (vars expr)) strG
              pure (expr, NE.head frees, new)
            once <- assertRightProp $ 
              safeAlphaRename expr (fv expr) old new
            twice <- assertRightProp $ 
              -- This may be an "unsafe" rename, since it could flip (and
              -- probably will) flip variables free variables to have the same
              -- name as bound variables (elsewhere in the term, since we only
              -- target free variables on the way in). It shouldn't matter though
              -- since we are just checking that this inverts
              alphaRename once (fv once) new old

            once /== expr
            twice === expr

    describe "alphaNormalizeWithVarMap" $ do
      it "consistent shadowing in right branch" $ do
        let exprTree =
              Abs ""
                (App
                  (Abs "" (Var ""))
                  (App (Var "") (Var ""))
                )
        (canonicalTree, varMap) <- assertRight $ alphaNormalizeWithVarMap S.empty exprTree
        canonicalTree `shouldBe`
          Abs 0
            (App
              (Abs 1 (Var 1))
              (App (Var 0) (Var 0))
            )
        S.fromList (foldMap (:[]) canonicalTree) `shouldBe`
          S.fromList (M.keys varMap)

      it "consistent shadowing in left branch" $ do
        let exprTree =
              Abs ""
                (App
                  (App (Var "") (Var ""))
                  (Abs "" (Var ""))
                )
        (canonicalTree, varMap) <- assertRight $ alphaNormalizeWithVarMap S.empty exprTree
        canonicalTree `shouldBe`
          Abs 0
            (App
              (App (Var 0) (Var 0))
              (Abs 1 (Var 1))
            )
        S.fromList (foldMap (:[]) canonicalTree) `shouldBe`
          S.fromList (M.keys varMap)

      it "consistent renaming of free variables" $ do
        let exprTree =
              Abs "x"
                (App
                  (App (Var "y") (Var "x"))
                  (Abs "z" (Var "y"))
                )
        (canonicalTree, varMap) <- assertRight $ alphaNormalizeWithVarMap (fv exprTree) exprTree
        canonicalTree `shouldBe`
          Abs 1
            (App
              (App (Var 0) (Var 1))
              (Abs 2 (Var 0))
            )
        S.fromList (foldMap (:[]) canonicalTree) `shouldBe`
          S.fromList (M.keys varMap)


      modifyMaxSuccess (const 10000) $
        it "should round trip" $
          hedgehog $ do
            exprTree <- forAll . exprG $ Gen.string (Range.linear 0 50) Gen.alpha
            (canonicalTree, varMap) <- assertRightProp $ alphaNormalizeWithVarMap (fv exprTree) exprTree
            -- liftIO $ print exprTree
            -- liftIO $ putStrLn . TL.unpack . printExprTree $ exprTree
            -- liftIO $ putStrLn . TL.unpack . printExprTree $ canonicalTree
            -- liftIO $ print varMap
            -- liftIO $ print (fv exprTree)
            case alphaReconstitute varMap canonicalTree of
              Failure e ->
                fail . fold $
                  intersperse
                    "\n"
                    [ "Couldn't reconstitute exprTree from canonicalTree."
                    , "Missing these indices " <> show e
                    , "From a varmap with these keys " <> show (M.keys varMap)
                    , "For exprTree: "
                    , TL.unpack . printExprTree $ exprTree
                    , "With canonicalTree: "
                    , TL.unpack . printExprTree $ canonicalTree
                    ]
              Success reconstitutedTree ->
                reconstitutedTree === exprTree
            S.fromList (foldMap (:[]) canonicalTree) ===
              S.fromList (M.keys varMap)

exprG :: (MonadGen m) => m a -> m (Expr a)
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
