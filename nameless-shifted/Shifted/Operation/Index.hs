module Shifted.Operation.Index where

import Data.Maybe (fromMaybe)
import Shifted.Var

-- openIdx
--   :: forall name expr
--    . (Vars expr, Eq name)
--   => Word
--   -> name
--   -> expr (Var Index name)
--   -> expr (Var Index name)
-- openIdx _ x =

open
  :: forall name expr
   . (Indexed expr, Vars expr, Eq name)
  => name
  -> expr (Var Index name)
  -> expr (Var Index name)
open x =
  sub $ \v idx -> var
    case v of
      DeBruijn i
        | idx == i -> Free x 0
        | otherwise -> DeBruijn i
      Free y i
        | y == x -> Free x (i + 1)
        | otherwise -> Free y i

-- open'
--   :: forall name expr
--    . (Indexed (expr name), Binder expr name, Vars (expr name), Eq name)
--   => expr name (Var Index name)
--   -> expr name (Var Index name)
-- open' = unbind open

closeIdx
  :: forall name expr
   . (Vars expr, Eq name)
  => Word
  -> name
  -> expr (Var Index name)
  -> expr (Var Index name)
closeIdx idx x =
  sub $ \v _ -> var $
    case v of
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

-- close'
--   :: forall name expr
--    . (Indexed (expr name), Binder expr name, Vars (expr name), Eq name)
--   => name
--   -> expr name (Var Index name)
--   -> expr name (Var Index name)
-- close' name = binder name . close name

-- | Remove a binder. This is effectively applying a lambda to an expression and substituting it in.
bindIdx
  :: forall name expr
   . (Vars (expr name))
  => Word
  -> expr name (Var Index name)
  -> expr name (Var Index name)
  -> expr name (Var Index name)
bindIdx idx u = sub \v w ->
  case v of
    DeBruijn i | idx == i -> u
    y -> var y

bindIdx'
  :: forall name expr
   . (Vars (expr name), Indexed (expr name))
  => Word
  -> Word
  -> expr name (Var Index name)
  -> expr name (Var Index name)
  -> expr name (Var Index name)
bindIdx' binders idx u = sub \v binders' ->
  case v of
    DeBruijn i | idx == i -> mapFreeIndices (+ (binders + binders')) u
    y -> var y

-- TODO: figure out what the index math is here,
-- and what we expect to call this on
bind
  :: forall name expr
   . (Indexed (expr name), Vars (expr name))
  => expr name (Var Index name)
  -> expr name (Var Index name)
  -> expr name (Var Index name)
bind u expr = bindIdx (fromMaybe 0 $ maxIdx expr) u expr

bind'
  :: forall name expr
   . (Indexed (expr name), Vars (expr name))
  => Word
  -> expr name (Var Index name)
  -> expr name (Var Index name)
  -> expr name (Var Index name)
bind' binders u expr = bindIdx' binders (fromMaybe 0 $ maxIdx expr) u expr

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
   . (Indexed (expr name), Vars (expr name), Eq name)
  => expr name (Var Index name)
  -> name
  -> expr name (Var Index name)
  -> expr name (Var Index name)
substitute u x expr =
  let nextIdx = maybe 0 (+ 1) $ maxIdx expr
   in bindIdx nextIdx u . closeIdx nextIdx x $ expr

substitute'
  :: forall name expr
   . (Indexed (expr name), Vars (expr name), Eq name)
  => Word
  -> expr name (Var Index name)
  -> name
  -> expr name (Var Index name)
  -> expr name (Var Index name)
substitute' binders u x expr =
  let nextIdx = maybe 0 (+ 1) $ maxIdx expr
   in bindIdx' binders nextIdx u . closeIdx nextIdx x $ expr

parSubstitute
  :: forall name expr
   . (Indexed (expr name), Vars (expr name), Eq name)
  => (expr name (Var Index name), expr name (Var Index name))
  -> (name, name)
  -> expr name (Var Index name)
  -> expr name (Var Index name)
parSubstitute (u, v) (y, x) = bind u . bind v . close y . close x

-- NOTE: No shift for De Bruijn indices
-- shift
--   :: forall name expr
--    . (Indexed (expr name), Vars (expr name), Eq name)
--   => name
--   -> expr name (Var Index name)
--   -> expr name (Var Index name)
-- shift x = open x . weaken x
