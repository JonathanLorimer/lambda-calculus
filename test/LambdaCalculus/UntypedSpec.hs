module LambdaCalculus.UntypedSpec where

import Data.Foldable (Foldable (..))
import Data.List (intersperse)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as M
import Data.Monoid (Endo (..))
import Data.Set qualified as S
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as TL
import Data.Validation (Validation (..))
import Hedgehog (MonadGen, forAll, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import LambdaCalculus.Untyped.Alpha (
  alphaNormalizeWithVarMap,
  alphaReconstitute,
  alphaRename,
  safeAlphaRename,
 )
import LambdaCalculus.Untyped.Beta (isNF, subst)
import LambdaCalculus.Untyped.Expr
import LambdaCalculus.Untyped.Printers (printExprTree)
import LambdaCalculus.Untyped.Vars (fv, vars)
import Test.Hspec
import Test.Hspec.Hedgehog (
  hedgehog,
  modifyMaxDiscardRatio,
  modifyMaxSuccess,
  (/==),
 )
import Test.Utils

spec :: Spec
spec = do
  describe "alpha" $ do
    describe "alphaRename" $ do
      modifyMaxDiscardRatio (const 1000) . modifyMaxSuccess (const 100) $
        it "should round trip" $
          hedgehog $ do
            (expr, old, new) <- forAll $ do
              let strG = Gen.string (Range.linear 0 50) Gen.alpha
              expr <- exprG strG
              frees <- Gen.mapMaybe (NE.nonEmpty . S.toList . fv) (pure expr)
              -- NOTE: we enforce the "safety" invariant for renaming here
              new <- Gen.filter (not . flip S.member (vars expr)) strG
              pure (expr, NE.head frees, new)
            once <-
              assertRightProp $
                safeAlphaRename expr (fv expr) old new
            twice <-
              assertRightProp $
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
        let exprTree :: Expr Text =
              Abs
                ""
                ( App
                    (Abs "" (Var ""))
                    (App (Var "") (Var ""))
                )
        (canonicalTree, varMap) <-
          assertRight $ alphaNormalizeWithVarMap S.empty exprTree
        canonicalTree
          `shouldBe` Abs
            0
            ( App
                (Abs 1 (Var 1))
                (App (Var 0) (Var 0))
            )
        S.fromList (foldMap (: []) canonicalTree)
          `shouldBe` S.fromList (M.keys varMap)

      it "consistent shadowing in left branch" $ do
        let exprTree :: Expr Text =
              Abs
                ""
                ( App
                    (App (Var "") (Var ""))
                    (Abs "" (Var ""))
                )
        (canonicalTree, varMap) <-
          assertRight $ alphaNormalizeWithVarMap S.empty exprTree
        canonicalTree
          `shouldBe` Abs
            0
            ( App
                (App (Var 0) (Var 0))
                (Abs 1 (Var 1))
            )
        S.fromList (foldMap (: []) canonicalTree)
          `shouldBe` S.fromList (M.keys varMap)

      it "consistent renaming of free variables" $ do
        let exprTree :: Expr Text =
              Abs
                "x"
                ( App
                    (App (Var "y") (Var "x"))
                    (Abs "z" (Var "y"))
                )
        (canonicalTree, varMap) <-
          assertRight $ alphaNormalizeWithVarMap (fv exprTree) exprTree
        canonicalTree
          `shouldBe` Abs
            1
            ( App
                (App (Var 0) (Var 1))
                (Abs 2 (Var 0))
            )
        S.fromList (foldMap (: []) canonicalTree)
          `shouldBe` S.fromList (M.keys varMap)

      modifyMaxSuccess (const 100) $
        it "should round trip" $
          hedgehog $ do
            exprTree <- forAll . exprG $ Gen.string (Range.linear 0 50) Gen.alpha
            (canonicalTree, varMap) <-
              assertRightProp $ alphaNormalizeWithVarMap (fv exprTree) exprTree
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
            S.fromList (foldMap (: []) canonicalTree)
              === S.fromList (M.keys varMap)

  describe "beta" $ do
    describe "subst" $ do
      it "should work with a variable" $ do
        let exprTree :: Expr Text = Abs "x" $ App (Var "y") (Var "x")
        result <- assertRight $ subst "y" exprTree $ Var "new"
        result `shouldBe` Abs "x" (App (Var "new") (Var "x"))

      it "should work with an abstraction" $ do
        let exprTree :: Expr Text = Abs "x" $ App (Var "y") (Var "x")
        result <- assertRight $ subst "y" exprTree $ Abs "x" (Var "x")
        result `shouldBe` Abs "x" (App (Abs "x" (Var "x")) (Var "x"))

      it "should work with an application" $ do
        let exprTree :: Expr Text = Abs "x" $ App (Var "y") (Var "x")
        result <- assertRight $ subst "y" exprTree $ App (Var "z") (Var "z")
        result `shouldBe` Abs "x" (App (App (Var "z") (Var "z")) (Var "x"))

      it "should rename if abstraction head is free in substitution body" $ do
        let exprTree :: Expr Text = Abs "x" $ App (Var "y") (Var "x")
        result <- assertRight $ subst "y" exprTree $ Var "x"
        result `shouldBe` Abs "0" (App (Var "x") (Var "0"))
      it "should not rename if there is no substitution in branch" $ do
        let exprTree :: Expr Text =
              App
                (Abs "x" $ App (Var "z") (Var "x"))
                (Abs "x" $ App (Var "y") (Var "x"))
        result <- assertRight $ subst "y" exprTree $ Var "x"
        result
          `shouldBe` App
            (Abs "x" $ App (Var "z") (Var "x"))
            (Abs "0" $ App (Var "x") (Var "0"))
    describe "isNF" $ do
      it "should return false for basic application of function" $ do
        let exprTree :: Expr Text = App (Abs "x" (Var "y")) (Var "x")
        isNF exprTree `shouldBe` False

      it "should return true top level lambda" $ do
        let exprTree :: Expr Text = Abs "x" $ App (Var "y") (Var "x")
        isNF exprTree `shouldBe` True

      it "should return true for term with no lambdas" $ do
        let exprTree :: Expr Text =
              appEndo
                ( foldMap
                    (Endo . App . Var . TL.singleton)
                    ['a' .. 'y']
                )
                (Var "z")
        isNF exprTree `shouldBe` True

      it "should return true for term with a stuck lambda" $ do
        let mkExprTree :: Expr Text -> Expr Text =
              appEndo
                ( foldMap
                    (Endo . App . Var . TL.singleton)
                    ['a' .. 'y']
                )
            exprTree = mkExprTree $ Abs "z" (mkExprTree (Var "z"))
        isNF exprTree `shouldBe` True

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
