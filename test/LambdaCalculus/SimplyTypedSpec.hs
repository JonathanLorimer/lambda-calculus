module LambdaCalculus.SimplyTypedSpec where

import Data.Map.Strict qualified as MS
import Data.Text (Text)
import LambdaCalculus.SimplyTyped.Expr
import Shifted.Nameless (withNameless)
import Test.Hspec

spec :: Spec
spec = do
  describe "whnfLvl" $ do
    it "(const id) \"z\"" $ do
      let _const' = _const (TyVar "α" |-> TyVar "α") (TyVar "β")
          _id' = _id @Text $ TyVar "α"
          actual = withNameless whnfLvl $ PTApp (PTApp _const' _id') (PTVar "z")
      actual `shouldBe` _id'
    it "ap const id ≡β const id" $ do
      let _const' = _const (TyVar "α" |-> TyVar "α") (TyVar "β")
          _id' = _id @Text $ TyVar "α"
          _ap' = _ap (TyVar "α" |-> TyVar "β" |-> TyVar "α") (TyVar "α")
          expr = (_ap' `PTApp` _const') `PTApp` _id'
          actual = withNameless whnfLvl expr
          expected = withNameless whnfLvl (_const' `PTApp` _id')
      actual `shouldBe` expected
    it "ap const (id id) ≡β const (id id)" $ do
      let _const' = _const (TyVar "α" |-> TyVar "α") (TyVar "β")
          _id' = _id @Text $ TyVar "α"
          _ap' = _ap (TyVar "α" |-> TyVar "β" |-> TyVar "α") (TyVar "α")
          expr = (_ap' `PTApp` _const') `PTApp` (_id' `PTApp` _id')
          actual = withNameless whnfLvl expr
          expected = withNameless whnfLvl (_const' `PTApp` (_id' `PTApp` _id'))
      actual `shouldBe` expected

  describe "nfLvl" $ do
    it "const (id \"z\") ≡β const \"z\"" $ do
      let _const' = _const (TyVar "α" |-> TyVar "α") (TyVar "β")
          _id' = _id @Text $ TyVar "α"
          actual = withNameless nfLvl $ PTApp _const' (PTApp _id' (PTVar "z"))
          expected = withNameless whnfLvl $ PTApp _const' (PTVar "z")
      isNF actual `shouldBe` True
      actual `shouldBe` expected
    it "ap const id ≡β const id" $ do
      let _const' = _const (TyVar "α" |-> TyVar "α") (TyVar "β")
          _id' = _id @Text $ TyVar "α"
          _ap' = _ap (TyVar "α" |-> TyVar "β" |-> TyVar "α") (TyVar "α")
          expr = (_ap' `PTApp` _const') `PTApp` _id'
          actual = withNameless nfLvl expr
          expected = withNameless nfLvl (_const' `PTApp` _id')
      actual `shouldBe` expected
    it "ap const (id id) ≡β const id" $ do
      let _const' = _const (TyVar "α" |-> TyVar "α") (TyVar "β")
          _id' = _id @Text $ TyVar "α"
          _ap' = _ap (TyVar "α" |-> TyVar "β" |-> TyVar "α") (TyVar "α")
          expr = (_ap' `PTApp` _const') `PTApp` (_id' `PTApp` _id')
          actual = withNameless nfLvl expr
          expected = withNameless nfLvl (_const' `PTApp` _id')
      actual `shouldBe` expected

  describe "whnfIdx" $ do
    it "const (id \"z\") ≡β const \"z\"" $ do
      let _const' = _const (TyVar "α" |-> TyVar "α") (TyVar "β")
          _id' = _id @Text $ TyVar "α"
          actual = withNameless whnfLvl $ PTApp (PTApp _const' _id') (PTVar "z")
      actual `shouldBe` _id'
    it "ap const id ≡β const id" $ do
      let _const' = _const (TyVar "α" |-> TyVar "α") (TyVar "β")
          _id' = _id @Text $ TyVar "α"
          _ap' = _ap (TyVar "α" |-> TyVar "β" |-> TyVar "α") (TyVar "α")
          expr = (_ap' `PTApp` _const') `PTApp` _id'
          actual = withNameless whnfIdx expr
          expected = withNameless whnfIdx (_const' `PTApp` _id')
      actual `shouldBe` expected
    it "ap const (id id) ≡β const (id id)" $ do
      let _const' = _const (TyVar "α" |-> TyVar "α") (TyVar "β")
          _id' = _id @Text $ TyVar "α"
          _ap' = _ap (TyVar "α" |-> TyVar "β" |-> TyVar "α") (TyVar "α")
          expr = (_ap' `PTApp` _const') `PTApp` (_id' `PTApp` _id')
          actual = withNameless whnfIdx expr
          expected = withNameless whnfIdx (_const' `PTApp` (_id' `PTApp` _id'))
      actual `shouldBe` expected

  describe "nfIdx" $ do
    it "const (id \"z\") ≡β const \"z\"" $ do
      let _const' = _const (TyVar "α" |-> TyVar "α") (TyVar "β")
          _id' = _id @Text $ TyVar "α"
          actual = withNameless nfIdx $ PTApp _const' (PTApp _id' (PTVar "z"))
          expected = withNameless whnfIdx $ PTApp _const' (PTVar "z")
      isNF actual `shouldBe` True
      actual `shouldBe` expected
    it "ap const id ≡β const id" $ do
      let _const' = _const (TyVar "α" |-> TyVar "α") (TyVar "β")
          _id' = _id @Text $ TyVar "α"
          _ap' = _ap (TyVar "α" |-> TyVar "β" |-> TyVar "α") (TyVar "α")
          expr = (_ap' `PTApp` _const') `PTApp` _id'
          actual = withNameless nfIdx expr
          expected = withNameless nfIdx (_const' `PTApp` _id')
      actual `shouldBe` expected
    it "ap const (id id) ≡β const id" $ do
      let _const' = _const (TyVar "α" |-> TyVar "α") (TyVar "β")
          _id' = _id @Text $ TyVar "α"
          _ap' = _ap (TyVar "α" |-> TyVar "β" |-> TyVar "α") (TyVar "α")
          expr = (_ap' `PTApp` _const') `PTApp` (_id' `PTApp` _id')
          actual = withNameless nfIdx expr
          expected = withNameless nfIdx (_const' `PTApp` _id')
      actual `shouldBe` expected

  describe "wellTyped" $ do
    it "id : α -> α" $ do
      wellTyped MS.empty (_id @Text $ TyVar "α")
        `shouldBe` (TyVar "α" |-> TyVar "α")
    it "const : α -> β -> α" $ do
      wellTyped MS.empty (_const @Text (TyVar "α") (TyVar "β"))
        `shouldBe` (TyVar "α" |-> TyVar "β" |-> TyVar "α")
    it "ap : (α -> β) -> α -> β" $ do
      let fTy = TyVar "α" |-> TyVar "β"
          xTy = TyVar "α"
          actual = wellTyped @Text @Text MS.empty $ _ap fTy xTy
          expected = fTy |-> xTy |-> TyVar "β"
      actual `shouldBe` expected
    it "ap : (α -> α) -> α -> α, id : α -> α ⊢ ap id : α -> α" $ do
      let _id' = _id @Text $ TyVar "α"
          _ap' = _ap (TyVar "α" |-> TyVar "α") (TyVar "α")
          expr = PTApp _ap' _id'
          actual = wellTyped MS.empty $ withNameless nfLvl expr
      actual `shouldBe` (TyVar "α" |-> TyVar "α")
