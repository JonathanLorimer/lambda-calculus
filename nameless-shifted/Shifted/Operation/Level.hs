module Shifted.Operation.Level where

import Shifted.Var
import Shifted.Binder

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
  sub $
    var . \case
      DeBruijn 0 -> Free x 0
      DeBruijn i -> DeBruijn (i - 1)
      Free y i
        | y == x -> Free x (i + 1)
        | otherwise -> Free y i

open'
  :: forall name expr
   . (Binder expr name, Vars (expr name), Eq name)
  => expr name (Var Level name)
  -> expr name (Var Level name)
open' = unbind open

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
  sub $
    var . \case
      Free y i
        | y == x && i == 0 -> DeBruijn 0
        | y == x && i > 0 -> Free y (i - 1)
        | otherwise -> Free y i
      DeBruijn n -> DeBruijn (n + 1)

close'
  :: forall name expr
   . (Binder expr name, Vars (expr name), Eq name)
  => name
  -> expr name (Var Level name)
  -> expr name (Var Level name)
close' name = binder name . close name

-- | Insert a binder. This is effectively adding a meaningless binder.
weaken
  :: forall name expr
   . (Binder expr name, Vars (expr name))
  => name
  -> expr name (Var Level name)
  -> expr name (Var Level name)
weaken name =
  binder name
    . sub
      ( var . \case
          DeBruijn i -> DeBruijn (i + 1)
          x -> x
      )

-- | Remove a binder. This is effectively applying a lambda to an expression and substituting it in.
bind
  :: forall name expr
   . (Binder expr name, Vars (expr name))
  => expr name (Var Level name)
  -> expr name (Var Level name)
  -> expr name (Var Level name)
bind u =
  unbind (\_ x -> x) . sub \case
    DeBruijn 0 -> u
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
   . (Binder expr name, Vars (expr name), Eq name)
  => expr name (Var Level name)
  -> name
  -> expr name (Var Level name)
  -> expr name (Var Level name)
substitute u x = bind u . close' x

parSubstitute
  :: forall name expr
   . (Binder expr name, Vars (expr name), Eq name)
  => (expr name (Var Level name), expr name (Var Level name))
  -> (name, name)
  -> expr name (Var Level name)
  -> expr name (Var Level name)
parSubstitute (u, v) (y, x) = bind u . bind v . close' y . close' x

shift
  :: forall name expr
   . (Binder expr name, Vars (expr name), Eq name)
  => name
  -> expr name (Var Level name)
  -> expr name (Var Level name)
shift x = open' . weaken x
