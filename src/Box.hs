{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}

module Box
  ( Committer (..),
    Emitter (..),
    Box (..),
    fire,
    glue,
    toListE,
    fromListE,
    CommitterF (..),
    EmitterF (..),
    BoxF (..),
    fromListEF,
    fromListC,
  ) where

import Prelude
import Data.Profunctor
import Control.Applicative
import Data.Functor.Contravariant
-- import Control.Monad.Hyper

-- data Box f g a b = Box { commit :: b -> g Bool, emit :: f (Maybe a) } deriving (Generic)

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

connect :: (Functor f) => Box f g a a -> f (g ())
connect (Box c e) = commit c <$> emit e

fromListE' :: (Applicative f, Alternative f) => [a] -> Emitter f a
fromListE' [] = Emitter empty
fromListE' (x:xs) = Emitter undefined

fire :: (Alternative f) => Box f g a a -> f (g ())
fire (Box c e) = commit c <$> emit e

glue :: (Alternative f, Alternative g) => Box f g a a -> f (g ())
glue b = fmap (foldr const empty) (many (fire b))

toListE :: (Alternative f) => Emitter f a -> f [a]
toListE e = many (emit e)

fromListE :: (Traversable t, Alternative f) => t a -> Emitter f a
fromListE xs = Emitter $ foldr (const . pure) empty xs

newtype CommitterF f a = CommitterF { commitF :: a -> f Bool }

instance Contravariant (CommitterF f) where
  contramap f (CommitterF a) = CommitterF (a . f)

newtype EmitterF f a = EmitterF { emitF :: f (Maybe a) }

instance (Functor f) => Functor (EmitterF f) where
  fmap f (EmitterF a) = EmitterF (fmap (fmap f) a)

data BoxF f g b a = BoxF { committerF :: CommitterF g b, emitterF :: EmitterF f a }

instance (Functor f) => Functor (BoxF f g b) where
  fmap f (BoxF c e) = BoxF c (fmap f e)

instance (Functor f) => Profunctor (BoxF f g) where
  dimap f g (BoxF c e) = BoxF (contramap f c) (fmap g e)

fromListEF :: (Traversable t, Applicative f, Applicative g) => t a -> Committer g a -> f ()
fromListEF xs c =
  foldr ((*>) . fmap (maybe (pure ()) (commit c)) . emit)
  (pure ()) (Emitter . pure . Just <$> xs)

fromListC :: (Traversable t, Applicative f) => t a -> Committer f a -> f ()
fromListC xs c =
  foldr ((*>) . commit c) (pure ()) xs
