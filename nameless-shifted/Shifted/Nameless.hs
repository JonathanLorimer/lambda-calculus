module Shifted.Nameless where

import Data.Kind
import Shifted.Var (Direction, Var)

class LocallyNameless (d :: Direction) (expr :: Type -> Type -> Type) where
  toNameless :: (Ord name) => expr name name -> expr name (Var d name)
  fromNameless :: expr name (Var d name) -> expr name name
