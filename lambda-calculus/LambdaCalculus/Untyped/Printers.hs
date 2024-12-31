module LambdaCalculus.Untyped.Printers where

import Control.Monad.Reader
import Data.Functor.Foldable
import Data.Text.Lazy (Text)
import Data.Text.Lazy.Builder qualified as TB
import LambdaCalculus.Untyped.Expr

printLambda :: (Show a, Show b) => Expr a b -> Text
printLambda =
  TB.toLazyText . cata \case
    VarF a -> TB.fromString $ show a
    AppF expr1 expr2 ->
      mconcat
        [ TB.singleton '('
        , expr1
        , TB.singleton ')'
        , TB.singleton '('
        , expr2
        , TB.singleton ')'
        ]
    AbsF a expr ->
      mconcat
        [ TB.singleton 'λ'
        , TB.fromString $ show a
        , TB.singleton '.'
        , expr
        ]

printExprTree :: (Show a, Show b) => Expr a b -> Text
printExprTree =
  TB.toLazyText . flip runReader 0 . cataA \case
    VarF x -> asks \indent ->
      mconcat
        [ TB.fromString (replicate indent ' ')
        , TB.fromString "[v] "
        , TB.fromString $ show x
        ]
    AppF expr1 expr2 -> do
      expr1' <- local (+ 2) expr1
      expr2' <- local (+ 2) expr2
      indent <- ask
      pure $
        mconcat
          [ TB.fromString (replicate indent ' ')
          , TB.fromString "[a]"
          , TB.singleton '\n'
          , expr1'
          , TB.singleton '\n'
          , expr2'
          ]
    AbsF x expr -> do
      expr' <- local (+ 2) expr
      indent <- ask
      pure $
        mconcat
          [ TB.fromString (replicate indent ' ')
          , TB.fromString "[λ] "
          , TB.fromString $ show x
          , TB.singleton '.'
          , TB.singleton '\n'
          , expr'
          ]
