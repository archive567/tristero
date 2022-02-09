{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

module Box
  (
    type (~>),
    -- * comms in the type
    Committer (..),
    Emitter (..),
    Box (..),
    connect,
    glue,
    nucleate,

    -- * more boxy
    CommitterB,
    EmitterB,
    BoxB,

    Nucleus(..),
    Hyper (..),
    HyperH,
) where

import Prelude hiding ((.), id)
import Data.Profunctor
import Data.Functor.Contravariant
import Data.Function ((&))
import Control.Monad.Trans.Maybe
import Data.Bifunctor.Flip
import Data.Functor.Const
import Control.Category

type f ~> g = forall a. f a -> g a

-- i ⊣ f ~> g ⊢ o

newtype Committer f a = Committer { commit :: a -> f () }

instance Contravariant (Committer f) where
  contramap f (Committer a) = Committer (a . f)

newtype Emitter f a = Emitter { emit :: f a }

instance (Functor f) => Functor (Emitter f) where
  fmap f (Emitter a) = Emitter (fmap f a)

data Box f g b a =
  Box { committer :: Committer g b, emitter :: Emitter f a }

instance (Functor f) => Functor (Box f g b) where
  fmap f (Box c e) = Box c (fmap f e)

instance (Functor f, Contravariant g) => Profunctor (Box f g) where
  dimap f g (Box c e) = Box (contramap f c) (fmap g e)

connect :: (f a -> b) -> Committer g b -> Emitter f a -> g ()
connect w c e = emit e & w & commit c

glue :: Box f g (f a) a -> g ()
glue (Box c e) = connect id c e

nucleate ::
  Functor f =>
  (f a -> f b) ->
  Committer g b ->
  Emitter f a ->
  f (g ())
nucleate n c e = emit e & n & fmap (commit c)

type CommitterB m a = Committer (MaybeT m) a
type EmitterB m a = Emitter (MaybeT m) a
type BoxB m b a = Box (MaybeT m) (MaybeT m) b a

newtype Nucleus p b = Nucleus (forall a. Nucleus (Flip p) a -> p a b)

newtype Hyper p a b = Hyper (Hyper (Flip p) a b -> p a b)

type HyperH a b = Hyper (Flip Const) a b

newtype a -&> b = Hyp ((b -&> a) -> b)

invoke :: (a -&> b) -> (b -&> a) -> b
invoke (Hyp f) = f

instance Category (-&>) where
  id = Hyp (`invoke` id)
  f . g = Hyp (\k -> invoke f (g . k))
