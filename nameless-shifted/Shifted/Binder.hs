{-# LANGUAGE FunctionalDependencies #-}
module Shifted.Binder where

import Data.Kind

class Binder (expr :: Type -> Type -> Type) (binder :: Type) | binder -> expr where
  -- an abstract representation of a binder constructor (usually lambda abstraction)
  binder :: binder -> expr binder a -> expr binder a

  -- A way to operate on a top level binder for the given expression, 
  -- if the expression is not a binder this function should do nothing.
  unbind
    :: (binder -> expr binder a -> expr binder a)
    -> expr binder a
    -> expr binder a

