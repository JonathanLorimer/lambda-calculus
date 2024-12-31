{-# LANGUAGE DataKinds #-}

module Shifted.Var (
  Var (..),
  Vars (..),
  Direction (..),
  Indexed (..),
  Levelled (..),
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
  sub
    :: (Var d name -> Word -> expr (Var d name))
    -> expr (Var d name)
    -> expr (Var d name)

class Indexed (expr :: Type -> Type) where
  maxIdx :: expr (Var Index name) -> Maybe Word

  mapFreeIndices
    :: (Var Index name -> Var Index name)
    -> expr (Var Index name)
    -> expr (Var Index name)

class Levelled (expr :: Type -> Type) where
  mapBoundLevels
    :: (Word -> Word)
    -> expr (Var Level name)
    -> expr (Var Level name)
