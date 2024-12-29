module Shifted.Generators where

import Hedgehog (MonadGen)
import Data.Text
import Example.Expr
import qualified Data.Text as T
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

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
