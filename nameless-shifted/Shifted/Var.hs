{-# LANGUAGE DataKinds #-}

module Shifted.Var (
  Var(..),
  Vars(..),
  Direction(..),
) where

import Data.Kind

data Direction = Index | Level

data Var (d :: Direction) a = Free a Word | DeBruijn Word
  deriving (Eq, Ord, Show)

class Vars (expr :: Type -> Type) where
  -- | an abstract representation of the variable constructor
  var :: Var d name -> expr (Var d name)

  -- | an abstract representation of an AST traversal running the
  -- provided function over each variable that we come across
  sub :: (Var d name -> expr (Var d name)) -> expr (Var d name) -> expr (Var d name)
