module LambdaCalculus.ExprSpec where

import Data.Validation (Validation (..))
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import LambdaCalculus.Expr (
  Expr (..),
  alphaNormalizeWithVarMap,
  alphaReconstitute,
  printExprTree,
 )
import Test.Hspec
import Test.Hspec.Hedgehog (MonadGen, forAll, hedgehog, (===))

import Control.Monad.IO.Class (liftIO)
import Data.Foldable (Foldable (..))
import Data.List (intersperse)
import qualified Data.Map.Strict as M
import qualified Data.Text.Lazy as TL
import Test.Hspec.QuickCheck (modifyMaxSuccess)
import qualified Data.Set as S

spec :: Spec
spec =
  describe "alpha renaming" $ do
      it "canonical renaming via alphaNormalize should round trip, important example 1" $ do
        let exprTree = 
              Abs "" 
                (App 
                  (Abs "" (Var "")) 
                  (App (Var "") (Var ""))
                )
        let (canonicalTree, varMap) = alphaNormalizeWithVarMap exprTree
        canonicalTree `shouldBe`
          Abs 0 
            (App 
              (Abs 1 (Var 1)) 
              (App (Var 0) (Var 0))
            )
        S.fromList (foldMap (:[]) canonicalTree) `shouldBe`
          S.fromList (M.keys varMap)

      it "canonical renaming via alphaNormalize should round trip, important example 2" $ do
        let exprTree = 
              Abs "" 
                (App 
                  (App (Var "") (Var ""))
                  (Abs "" (Var "")) 
                )
        let (canonicalTree, varMap) = alphaNormalizeWithVarMap exprTree
        canonicalTree `shouldBe`
          Abs 0 
            (App 
              (App (Var 0) (Var 0))
              (Abs 1 (Var 1)) 
            )
        S.fromList (foldMap (:[]) canonicalTree) `shouldBe`
          S.fromList (M.keys varMap)
          

      modifyMaxSuccess (const 100) $
        xit "canonical renaming via alphaNormalize should round trip" $
          hedgehog $ do
            exprTree <- forAll . exprG $ Gen.string (Range.linear 0 50) Gen.alpha
            let (canonicalTree, varMap) = alphaNormalizeWithVarMap exprTree
            liftIO $ print exprTree
            liftIO $ putStrLn . TL.unpack . printExprTree $ exprTree
            liftIO $ putStrLn . TL.unpack . printExprTree $ canonicalTree
            liftIO $ print varMap
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
