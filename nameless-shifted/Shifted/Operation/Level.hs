module Shifted.Operation.Level where

import Shifted.Var

-- | Opens an expression under a lambda abstraction a.k.a move under a binder.
--
-- Note that because we keep the expression
-- language abstract, this function is not meant to be applied to an actual lambda term, but
-- instead is meant to be used when one has a lambda term in hand, this is reflected by the
-- fact that the function accepts a 'name' (the lambda head) _and_ an 'expr' (the lambda body)
open
  :: forall name expr
   . (Vars expr, Eq name)
  => name
  -> expr (Var Level name)
  -> expr (Var Level name)
open x =
  sub \v w -> var $
    case v of
      DeBruijn 0 -> Free x 0
      DeBruijn i -> DeBruijn (i - 1)
      Free y i
        | y == x -> Free x (i + 1)
        | otherwise -> Free y i

-- | Closes an expression with a lambda abstraction a.k.a moves out of a binder.
--
-- Note that because we keep the expression
-- language abstract, this function does not produce a lambda expression, but _just_ the lambda
-- body. It is left to the caller to wrap the resulting body with a lambda where the head should
-- be equivalent to the name provided (or ellided if fully using de bruijn).
close
  :: forall name expr
   . (Vars expr, Eq name)
  => name
  -> expr (Var Level name)
  -> expr (Var Level name)
close x =
  sub \v w -> var $
    case v of
      Free y i
        | y == x && i == 0 -> DeBruijn 0
        | y == x && i > 0 -> Free y (i - 1)
        | otherwise -> Free y i
      DeBruijn n -> DeBruijn (n + 1)

-- | Insert a binder. This is effectively adding a meaningless binder.
weaken
  :: forall name expr
   . (Vars (expr name))
  => name
  -> expr name (Var Level name)
  -> expr name (Var Level name)
weaken name = sub \v w -> var $
  case v of
    DeBruijn i -> DeBruijn (i + 1)
    x -> x

-- | Remove a binder. This is effectively applying a lambda to an expression and substituting it in.
bind
  :: forall name expr
   . (Vars (expr name))
  => expr name (Var Level name)
  -> expr name (Var Level name)
  -> expr name (Var Level name)
bind u = sub \v w ->
  case v of
    DeBruijn 0 -> u
    DeBruijn i -> var $ DeBruijn (i - 1)
    y -> var y

bind'
  :: forall name expr
   . (Levelled (expr name), Vars (expr name))
  => Word
  -> expr name (Var Level name)
  -> expr name (Var Level name)
  -> expr name (Var Level name)
bind' binders u = sub \v binders' ->
  case v of
    DeBruijn 0 -> mapBoundLevels (+ (binders + binders')) u
    DeBruijn i -> var $ DeBruijn (i - 1)
    y -> var y

rename
  :: forall name expr
   . (Vars expr, Eq name)
  => name
  -> name
  -> expr (Var Level name)
  -> expr (Var Level name)
rename y x = open y . close x

parRename
  :: forall name expr
   . (Vars expr, Eq name)
  => (name, name)
  -> (name, name)
  -> expr (Var Level name)
  -> expr (Var Level name)
parRename (y, w) (x, z) = open y . open w . close z . close x

substitute
  :: forall name expr
   . (Vars (expr name), Eq name)
  => expr name (Var Level name)
  -> name
  -> expr name (Var Level name)
  -> expr name (Var Level name)
substitute u x = bind u . close x

substitute'
  :: forall name expr
   . (Levelled (expr name), Vars (expr name), Eq name)
  => Word
  -> expr name (Var Level name)
  -> name
  -> expr name (Var Level name)
  -> expr name (Var Level name)
substitute' binders u x = bind' binders u . close x

parSubstitute
  :: forall name expr
   . (Vars (expr name), Eq name)
  => (expr name (Var Level name), expr name (Var Level name))
  -> (name, name)
  -> expr name (Var Level name)
  -> expr name (Var Level name)
parSubstitute (u, v) (y, x) = bind u . bind v . close y . close x

shift
  :: forall name expr
   . (Vars (expr name), Eq name)
  => name
  -> expr name (Var Level name)
  -> expr name (Var Level name)
shift x = open x . weaken x
