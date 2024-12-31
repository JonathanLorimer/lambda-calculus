module Shifted.NamelessSpec where

import Hedgehog (annotateShow, forAll, (===))
import Shifted.Generators
import Shifted.Nameless (LocallyNameless (..))
import Shifted.Var (Direction (..))
import Test.Hspec
import Test.Hspec.Hedgehog (
  hedgehog,
 )
import Test.Utils (runs)

spec :: Spec
spec = do
  describe "nameless" $ do
    runs 100 $ it "fromNameless • toNameless" $ hedgehog $ do
      expr <- forAll $ exprG textG
      let nameless = toNameless @Level expr
      annotateShow nameless
      fromNameless nameless === expr
