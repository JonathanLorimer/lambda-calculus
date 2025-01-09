module LambdaCalculus.UntypedSpec where

import LambdaCalculus.Untyped.Expr
import Shifted.Nameless (withNameless)
import Test.Hspec

spec :: Spec
spec = do
  describe "whnfLvl" $ do
    it "const (id \"z\") ≡β const \"z\"" $ do
      let actual =
            withNameless whnfLvl $
              App (App _const _id) (Var "z")
      actual `shouldBe` _id
    it "ap const id ≡β const id" $ do
      let expr = (_ap `App` _const) `App` _id
          actual = withNameless whnfLvl expr
          expected = withNameless whnfLvl (_const `App` _id)
      actual `shouldBe` expected
    it "ap const (id id) ≡β const (id id)" $ do
      let expr = (_ap `App` _const) `App` (_id `App` _id)
          actual = withNameless whnfLvl expr
          expected = withNameless whnfLvl (_const `App` (_id `App` _id))
      actual `shouldBe` expected
  describe "nfLvl" $ do
    it "const (id \"z\") ≡β const \"z\"" $ do
      let actual =
            withNameless nfLvl $
              App _const (App _id (Var "z"))
          expected = withNameless whnfLvl $ App _const (Var "z")
      isNF actual `shouldBe` True
      actual `shouldBe` expected
    it "ap const id ≡β const id" $ do
      let expr = (_ap `App` _const) `App` _id
          actual = withNameless nfLvl expr
          expected = withNameless nfLvl (_const `App` _id)
      actual `shouldBe` expected
    it "ap const (id id) ≡β const id" $ do
      let expr = (_ap `App` _const) `App` (_id `App` _id)
          actual = withNameless nfLvl expr
          expected = withNameless nfLvl (_const `App` _id)
      actual `shouldBe` expected
  describe "whnfIdx" $ do
    it "const (id \"z\") ≡β const \"z\"" $ do
      let actual =
            withNameless whnfIdx $
              App (App _const _id) (Var "z")
      actual `shouldBe` _id
    it "ap const id ≡β const id" $ do
      let expr = (_ap `App` _const) `App` _id
          actual = withNameless whnfIdx expr
          expected = withNameless whnfIdx (_const `App` _id)
      actual `shouldBe` expected
    it "ap const (id id) ≡β const (id id)" $ do
      let expr = (_ap `App` _const) `App` (_id `App` _id)
          actual = withNameless whnfIdx expr
          expected = withNameless whnfIdx (_const `App` (_id `App` _id))
      actual `shouldBe` expected
  describe "nfIdx" $ do
    it "const (id \"z\") ≡β const \"z\"" $ do
      let actual =
            withNameless nfIdx $
              App _const (App _id (Var "z"))
          expected = withNameless whnfIdx $ App _const (Var "z")
      isNF actual `shouldBe` True
      actual `shouldBe` expected
    it "ap const id ≡β const id" $ do
      let expr = (_ap `App` _const) `App` _id
          actual = withNameless nfIdx expr
          expected = withNameless nfIdx (_const `App` _id)
      actual `shouldBe` expected
    it "ap const (id id) ≡β const id" $ do
      let expr = (_ap `App` _const) `App` (_id `App` _id)
          actual = withNameless nfIdx expr
          expected = withNameless nfIdx (_const `App` _id)
      actual `shouldBe` expected
