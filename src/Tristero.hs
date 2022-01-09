{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}

module Tristero
  ( Thing,
    Optic,
    AdapterP,
    LensP,
    PrismP,
    TraversalP,

    Adapter (..),
    type (::~>),
    Lens (..),
    Prism (..),
    Traversal (..),
  ) where

import Prelude
import Data.Profunctor
import Data.Bifunctor
import Data.Function
import Data.Profunctor.Monoidal
import Control.Applicative
import Data.Functor.Contravariant
import Control.Monad

-- * The Thing heirarchy

type Thing d p q a b s t = p a b `d` q s t

type Optic p a b s t = Thing (->) p p a b s t

type AdapterP a b s t = ∀ p. Profunctor p ⇒ Optic p a b s t

-- from https://bartoszmilewski.com/2018/02/20/free-monoidal-profunctors/
-- natural transformation between two profunctors
type p ::~> q = forall a b. Thing (->) p q a b a b

type LensP a b s t = ∀p . Strong p ⇒ Optic p a b s t

type PrismP a b s t = ∀p . Choice p ⇒ Optic p a b s t

type TraversalP a b s t =
  ∀ p.
  (Strong p,Costrong p,Monoidal p) ⇒
  Optic p a b s t

-- * original profunctor optics paper

-- | adapter
data Adapter a b s t = Adapter { from :: s → a, to :: b → t } deriving (Functor)

instance Profunctor (Adapter a b) where
--instance (forall a. Functor (Adapter a b s)) => Profunctor (Adapter a b) where
  dimap f g (Adapter o i) = Adapter (o . f) (g . i)

-- | lens
data Lens a b s t = Lens {view :: s → a, update :: (b, s) → t} deriving (Functor)

instance Profunctor (Lens a b) where
  dimap f g (Lens v u) = Lens (v . f) (g . u . cross id f)

instance Strong (Lens a b) where
  first' (Lens v u) = Lens (v . fst) (fork (u . cross id fst) (snd . snd))
  second' (Lens v u) = Lens (v . snd) (fork (fst . snd) (u . cross id snd))

fork :: (t -> a) -> (t -> b) -> t -> (a, b)
fork f g x = (f x, g x)

cross :: (t1 -> a) -> (t2 -> b) -> (t1, t2) -> (a, b)
cross f g (x, y) = (f x, g y)

-- | prism
data Prism a b s t = Prism { match :: s → Either t a, build :: b → t }

instance Functor (Prism a b s) where
  fmap f (Prism m b) = Prism (first f . m) (f . b)

instance Profunctor (Prism a b) where
  dimap f g (Prism m b) = Prism (plus g id . m . f) (g . b)

instance Choice (Prism a b) where
  left' (Prism m b) = Prism (either (plus Left id . m) (Left . Right)) (Left . b)
  right' (Prism m b) = Prism (either (Left . Left) (plus Right id . m)) (Right . b)

plus :: (t1 -> a) -> (t2 -> b) -> Either t1 t2 -> Either a b
plus f _ (Left x) = Left (f x)
plus _ g (Right y) = Right (g y)

-- | Traversal
newtype Traversal a b s t = Traversal {extract :: s → FunList a b t} deriving (Functor)

data FunList a b t = Done t | More a (FunList a b (b → t))

instance Functor (FunList a b) where
  fmap f (Done t) = Done (f t)
  fmap f (More x l) = More x (fmap (f .) l)

instance Applicative (FunList a b) where
  pure = Done
  (Done f) <*> l  = fmap f l
  (More x l) <*> l' = More x (fmap flip l <*> l')


instance Profunctor (Traversal a b) where
  dimap f g (Traversal h) = Traversal (fmap g . h . f)

instance Strong (Traversal a b) where
  first' (Traversal h) = Traversal (\(s,c) -> fmap (,c) (h s))
  second' (Traversal h) = Traversal (\(c,s) -> fmap (c,) (h s))

instance Choice (Traversal a b) where
  left' (Traversal h) = Traversal (either (fmap Left . h) (Done . Right))
  right' (Traversal h) = Traversal (either (Done . Left) (fmap Right . h))

{-
instance Monoidal (Traversal a b) where
  par (Traversal h) (Traversal k) = Traversal undefined -- (h,k)
  empty = Traversal pure

-}


-- | an alternative to Star worth comparing.
newtype UpStar f a b = UpStar { unUpStar:: a -> f b } deriving (Functor)

-- instance (Functor f) => Costrong (UpStar f) where

instance Functor f ⇒ Profunctor (UpStar f) where
  dimap f g (UpStar h) = UpStar (fmap g . h . f)

instance Functor f => Strong (UpStar f) where
  first' (UpStar f) = UpStar (rstrength . cross f id)
  second' (UpStar f) = UpStar (lstrength . cross id f)

rstrength :: Functor f ⇒ (f a, b) → f (a, b)
rstrength (fx, y) = fmap (,y) fx

lstrength :: Functor f ⇒ (a, f b) → f (a, b)
lstrength (x, fy) = fmap (x,) fy

instance Applicative f ⇒ Choice (UpStar f) where
  left' (UpStar f) = UpStar (either (fmap Left . f) (pure . Right))
  right' (UpStar f) = UpStar (either (pure . Left) (fmap Right . f))

instance Applicative f ⇒ Monoidal (UpStar f) where
  pempty = UpStar pure
  pappend h k = UpStar (pair (unUpStar h) (unUpStar k))

pair :: Applicative f ⇒ (a → f b) → (c → f d) → (a,c) → f (b, d)
pair h k (x, y) = (,) <$> h x <*> k y

-- traverseOf :: Traversal a b s t -> (∀ f. Applicative f ⇒ (a -> f b) -> s -> f t)
-- traverseOf p f = undefined -- runStar (p (Star f))
