module Shifted.Operation.Index where

import Data.Maybe (fromMaybe)
import Shifted.Binder
import Shifted.Var

openIdx
  :: forall name expr
   . (Vars expr, Eq name)
  => Word
  -> name
  -> expr (Var Index name)
  -> expr (Var Index name)
openIdx idx x =
  sub $
    var . \case
      DeBruijn i
        | idx == i -> Free x 0
        | otherwise -> DeBruijn i
      Free y i
        | y == x -> Free x (i + 1)
        | otherwise -> Free y i

open
  :: forall name expr
   . (Indexed expr, Vars expr, Eq name)
  => name
  -> expr (Var Index name)
  -> expr (Var Index name)
open x expr = openIdx (maybe 0 (+ 1) $ maxIdx expr) x expr

open'
  :: forall name expr
   . (Indexed (expr name), Binder expr name, Vars (expr name), Eq name)
  => expr name (Var Index name)
  -> expr name (Var Index name)
open' = unbind open

closeIdx
  :: forall name expr
   . (Vars expr, Eq name)
  => Word
  -> name
  -> expr (Var Index name)
  -> expr (Var Index name)
closeIdx idx x =
  sub $
    var . \case
      Free y i
        | y == x && i == 0 -> DeBruijn idx
        | y == x && i > 0 -> Free y (i - 1)
        | otherwise -> Free y i
      n -> n

close
  :: forall name expr
   . (Indexed expr, Vars expr, Eq name)
  => name
  -> expr (Var Index name)
  -> expr (Var Index name)
close x expr = closeIdx (maybe 0 (+ 1) $ maxIdx expr) x expr

close'
  :: forall name expr
   . (Indexed (expr name), Binder expr name, Vars (expr name), Eq name)
  => name
  -> expr name (Var Index name)
  -> expr name (Var Index name)
close' name = binder name . close name

-- | Insert a binder. This is effectively adding a meaningless binder.
weaken
  :: forall name expr
   . (Binder expr name, Vars (expr name))
  => name
  -> expr name (Var Index name)
  -> expr name (Var Index name)
weaken = binder

-- | Remove a binder. This is effectively applying a lambda to an expression and substituting it in.
bindIdx
  :: forall name expr
   . (Binder expr name, Vars (expr name))
  => Word
  -> expr name (Var Index name)
  -> expr name (Var Index name)
  -> expr name (Var Index name)
bindIdx idx u =
  unbind (\_ x -> x) . sub \case
    DeBruijn i | idx == i -> u
    y -> var y

bind
  :: forall name expr
   . (Indexed (expr name), Binder expr name, Vars (expr name))
  => expr name (Var Index name)
  -> expr name (Var Index name)
  -> expr name (Var Index name)
bind u expr = bindIdx (fromMaybe 0 $ maxIdx expr) u expr

rename
  :: forall name expr
   . (Indexed expr, Vars expr, Eq name)
  => name
  -> name
  -> expr (Var Index name)
  -> expr (Var Index name)
rename y x = open y . close x

parRename
  :: forall name expr
   . (Indexed expr, Vars expr, Eq name)
  => (name, name)
  -> (name, name)
  -> expr (Var Index name)
  -> expr (Var Index name)
parRename (y, w) (x, z) =
  open y
    . open w
    . close z
    . close x

substitute
  :: forall name expr
   . (Indexed (expr name), Binder expr name, Vars (expr name), Eq name)
  => expr name (Var Index name)
  -> name
  -> expr name (Var Index name)
  -> expr name (Var Index name)
substitute u x = bind u . close' x

parSubstitute
  :: forall name expr
   . (Indexed (expr name), Binder expr name, Vars (expr name), Eq name)
  => (expr name (Var Index name), expr name (Var Index name))
  -> (name, name)
  -> expr name (Var Index name)
  -> expr name (Var Index name)
parSubstitute (u, v) (y, x) = bind u . bind v . close' y . close' x

shift
  :: forall name expr
   . (Indexed (expr name), Binder expr name, Vars (expr name), Eq name)
  => name
  -> expr name (Var Index name)
  -> expr name (Var Index name)
shift x = open' . weaken x
