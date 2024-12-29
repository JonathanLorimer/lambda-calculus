module Shifted.Var (
  Var(..),
  Vars(..)
) where

import Data.Kind

data Var a = Free a Word | DeBruijn Word
  deriving (Eq, Ord, Show)

class Vars (expr :: Type -> Type) where
  -- | an abstract representation of the variable constructor
  var :: Var name -> expr (Var name)

  -- | an abstract representation of an AST traversal running the
  -- provided function over each variable that we come across
  sub :: (Var name -> expr (Var name)) -> expr (Var name) -> expr (Var name)
