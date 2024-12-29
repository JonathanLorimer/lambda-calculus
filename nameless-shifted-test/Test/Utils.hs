module Test.Utils where

import Hedgehog (PropertyT, annotate, annotateShow, failure)
import Test.HUnit (assertFailure)

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
