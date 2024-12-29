{-# LANGUAGE FunctionalDependencies #-}

module Shifted.Primitive where

import Data.Kind

data Var a = Name a Word | DeBruijn Word
  deriving (Eq, Ord, Show)

class Vars (expr :: Type -> Type) where
  -- | an abstract representation of the variable constructor
  var :: Var name -> expr (Var name)

  -- | an abstract representation of an AST traversal running the
  -- provided function over each variable that we come across
  varElim :: (Var name -> expr (Var name)) -> expr (Var name) -> expr (Var name)

class Binder (expr :: Type -> Type -> Type) (binder :: Type) | binder -> expr where
  -- an abstract representation of a binder constructor (usually lambda abstraction)
  binder :: binder -> expr binder a -> expr binder a

  -- | an abstract representation of an AST traversal running the
  -- provided function over each binder that we come across
  binderElim
    :: (binder -> expr binder a -> expr binder a)
    -> expr binder a
    -> expr binder a

class LocallyNameless (expr :: Type -> Type -> Type) where
  toNameless :: (Ord name) => expr name name -> expr name (Var name)
  fromNameless :: expr name (Var name) -> expr name name

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
  -> expr (Var name)
  -> expr (Var name)
open x =
  varElim $
    var . \case
      DeBruijn 0 -> Name x 0
      DeBruijn i -> DeBruijn (i - 1)
      Name y i
        | y == x -> Name x (i + 1)
        | otherwise -> Name y i

open'
  :: forall name expr
   . (Binder expr name, Vars (expr name), Eq name)
  => expr name (Var name)
  -> expr name (Var name)
open' = binderElim open

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
  -> expr (Var name)
  -> expr (Var name)
close x =
  varElim $
    var . \case
      Name y i
        | y == x && i == 0 -> DeBruijn 0
        | y == x && i > 0 -> Name y (i - 1)
        | otherwise -> Name y i
      DeBruijn n -> DeBruijn (n + 1)

close'
  :: forall name expr
   . (Binder expr name, Vars (expr name), Eq name)
  => name
  -> expr name (Var name)
  -> expr name (Var name)
close' name = binder name . close name

-- | Insert a binder. This is effectively adding a meaningless binder.
weaken
  :: forall name expr
   . (Binder expr name, Vars (expr name))
  => name
  -> expr name (Var name)
  -> expr name (Var name)
weaken name =
  binder name
    . varElim
      ( var . \case
          DeBruijn i -> DeBruijn (i + 1)
          x -> x
      )

-- | Remove a binder. This is effectively applying a lambda to an expression and substituting it in.
bind
  :: forall name expr
   . (Binder expr name, Vars (expr name))
  => expr name (Var name)
  -> expr name (Var name)
  -> expr name (Var name)
bind u =
  binderElim (\_ x -> x) . varElim \case
    DeBruijn 0 -> u
    DeBruijn i -> var $ DeBruijn (i + 1)
    y -> var y

rename
  :: forall name expr
   . (Vars expr, Eq name)
  => name
  -> name
  -> expr (Var name)
  -> expr (Var name)
rename y x = open y . close x

parRename
  :: forall name expr
   . (Vars expr, Eq name)
  => (name, name)
  -> (name, name)
  -> expr (Var name)
  -> expr (Var name)
parRename (y, w) (x, z) = open y . open w . close z . close x

substitute
  :: forall name expr
   . (Binder expr name, Vars (expr name), Eq name)
  => expr name (Var name)
  -> name
  -> expr name (Var name)
  -> expr name (Var name)
substitute u x = bind u . close x

parSubstitute
  :: forall name expr
   . (Binder expr name, Vars (expr name), Eq name)
  => (expr name (Var name), expr name (Var name))
  -> (name, name)
  -> expr name (Var name)
  -> expr name (Var name)
parSubstitute (u, v) (y, x) = bind u . bind v . close y . close x

shift
  :: forall name expr
   . (Binder expr name, Vars (expr name), Eq name)
  => name
  -> expr name (Var name)
  -> expr name (Var name)
shift x = open x . weaken x
