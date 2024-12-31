module Shifted.Nameless where

import Data.Kind
import Shifted.Var (Direction, Var)

-- TODO: Add some sort of error option, either have the functions return an
-- either, or have some associated error functor type that can be set to
-- Identity if necessary
class LocallyNameless (d :: Direction) (expr :: Type -> Type -> Type) where
  toNameless :: (Ord name) => expr name name -> expr name (Var d name)
  fromNameless :: expr name (Var d name) -> expr name name

withNameless
  :: (LocallyNameless d expr, Ord a)
  => (expr a (Var d a) -> expr a (Var d a))
  -> expr a a
  -> expr a a
withNameless f = fromNameless . f . toNameless
