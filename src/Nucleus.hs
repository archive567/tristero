{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}

module Nucleus
  (
  ) where

import Prelude
import Control.Monad
import Control.Applicative
import Data.Profunctor
import GHC.Generics
import Data.Functor.Identity
import Data.String
import Data.Bool
import Data.Functor
import Yaya.Functor
import Data.Functor.Compose
import Data.Distributive
import Control.Monad.Trans.Maybe
import Data.Maybe
import Data.Distributive

{-

Take a Profunctor and split it into three:

- the incoming contravariant input,
- the outgoing covariant output, and
- a Nucleus, which must be a natural transformation.

Contra => Nucleus => Covar

Productors compose via connecting up a Covar and a Contra, again via a nucleus.

(Contra => Nucleus => Covar) => Nucleus => (Contra => Nucleus => Covar)

So both associations are common:

Covar => Nucleus => Contra

Contra => Nucleus => Covar

A nucleus can be composed between two profuctors, but we tend to modify the nucleus of the first or second profunctor so that the outgoing Covar of the first profunctor fits directly to the incoming Contra of the second profunctor.

Calling a natural transformation a nucleus then reduces the visibility that a natural transformation is also what is outside profunctors allowing them to compose and computations to close.

monads over posets are called closure operators
comonads over posets are the interior operators
the (Kleisli) cofree coalgebra construction

the (EilenbergMoore) algebra construction EM : Mnd −→ Adj (and the coalgebra construction EC : Cmn −→ Adj
that is not displayed) captures the final resolutions of monads (resp. comonads)

file:///Users/tonyday/Downloads/2004.07353.pdf

coKleisli arrows of comonads

-}



newtype Algebra f a = Algebra { unalgebra :: f a -> a}

newtype Coalgebra f a = Coalgebra { uncoalgebra :: a -> f a}

type a ⊣ f = Coalgebra f a

type f ⊢ a = Algebra f a

type f ~> g = forall x. f x -> g x

data Pro f g a b = Pro
  { i :: Coalgebra f a,
    o :: Algebra g b,
    nat :: f ~> g
  }

makePro :: a ⊣ f -> f ~> g -> g ⊢ a -> a -> a
makePro i nat o a = (unalgebra o) (nat ((uncoalgebra i) a))

-- type Pro' a ⊣ f ~> g ⊢ b = Pro f g a b

-- type BoxB f g a b = Pro f g a b

--print' :: Pro Identity IO Int ()
--print' = Pro show putStrLn id

-- file:///Users/tonyday/Downloads/2004.07353.pdf
-- https://hackage.haskell.org/package/type-operators-0.2.0.0/docs/Control-Type-Operator.html
-- https://doisinkidney.com/pdfs/algebras-for-weighted-search.pdf

-- | Contra and Covar are dual to each other in what way?
--
-- a is a contravariant value
-- f b is extra context
--
-- TODO: use a -> f a
newtype Contra a f b = Contra { uncontra :: a -> f b }

instance HFunctor (Contra a) where
  hmap nat (Contra f) = Contra $ nat . f

newtype Covar g c = Covar { uncovar :: g c }

instance HFunctor Covar where
  hmap nat (Covar e) = Covar (nat e)

instance HFunctor Coalgebra where
  hmap nat (Coalgebra f) = Coalgebra $ nat . f

data ProF f g a b = ProF
  { coalgP :: Coalgebra f a,
    covarP :: Covar g b,
    natP :: f ~> g
  }

-- | A Shell is a product of a Contra and a Covar. It is it's own dual in the sense that it describes the connection points that can turn a nucleus into a profunctor, but can also wire up the profunctor to its outside context (it's closure). The Shell doesn't care which is which.
--
--
--
data Shell f g a b c = Shell
  { contra :: Contra a f b,
    covar :: Covar g c
  }

data Shell' f g a b = Shell'
  { coalg :: Coalgebra f a,
    covar' :: Covar g b
  }

-- | 2 adjoints walk into a bar. I'll have what we're having, and the same for my buddy. Coming right up.
hmap2 :: f ~> f' -> g ~> g' -> Shell f g a b c -> Shell f' g' a b c
hmap2 natf natg (Shell i o) = Shell (hmap natf i) (hmap natg o)

-- | 2 adjoints walk into a bar. I'll have what we're having, and the same for my buddy. Coming right up.
hmap2' :: f ~> f' -> g ~> g' -> Shell' f g a b -> Shell' f' g' a b
hmap2' natf natg (Shell' i o) = Shell' (hmap natf i) (hmap natg o)

-- | Mapping a notion of Contra failure (as a functor across the nucleus)
--
--
type Box f g a b = Shell f (Compose Maybe g) a Bool b

type Box' f g a b = Shell' f (Compose Maybe g) a b

hmapBox :: f ~> f' -> g ~> g' -> Box f g a c -> Box f' g' a c
hmapBox natf natg (Shell i o) = Shell (hmap natf i) (hmap (hmap natg) o)

hmapBox' :: f ~> f' -> g ~> g' -> Box' f g a c -> Box' f' g' a c
hmapBox' natf natg (Shell' i o) = Shell' (hmap natf i) (hmap (hmap natg) o)

-- * closures
close2 :: Functor g => Shell f g a b a -> g (f b)
close2 (Shell (Contra contra) (Covar covar)) = fmap contra covar

close2' :: Functor g => Shell' f g a a -> g (f a)
close2' (Shell' (Coalgebra contra) (Covar covar)) = fmap contra covar

close_ :: Functor g => Shell f g a x a -> g ()
close_ (Shell (Contra contra) (Covar covar)) = void $ fmap contra covar

closeA :: (Applicative f, Functor g) =>
     Shell f g a Bool (Maybe a) -> g (f Bool)
closeA (Shell (Contra contra) (Covar covar)) =
  fmap (maybe (pure False) contra) covar

closeA' :: (Applicative g) => Shell' f (Compose Maybe g) a b -> g (Maybe b)
closeA' (Shell' (Coalgebra _) (Covar covar)) =
  maybe (pure Nothing) (fmap Just) $ getCompose covar

{-
instance Distributive Maybe
  where
    distribute a = maybe (pure Nothing) (Just) a

-}

distribMaybe :: (Applicative f) => Compose Maybe f a -> Compose f Maybe a
distribMaybe = Compose . maybe (pure Nothing) (fmap Just) . getCompose

-- * looping
loopM :: Monad g => Shell g g a Bool (Maybe a) -> g ()
loopM s@(Shell (Contra contra) (Covar covar)) =
  go s
  where
    go s' = do
      a <- covar
      c' <- maybe (pure False) contra a
      bool (go s') (pure ()) c'

evalB :: Shell Identity Identity a b a -> b
evalB (Shell (Contra contra) (Covar covar)) =
  runIdentity $ runIdentity $ fmap contra covar

{-
-- | composition of monadic shells
-- dotM :: (Monad m) => Shell m m a x b -> Shell m m b x c -> m (Shell m m a x c)
dotM ::
  Monad m =>
  ContraC f m a b ->
  ContraC m g b c ->
  m (ContraC f g a c)
dotM (Shell contra covar) (Shell contra' covar') =
  loopM (Shell contra' covar)

-}



{-
-- * composition

-- | composition of monadic shells
dotM :: (Monad m) => Shell m m a x b -> Shell m m b x c -> m (Shell m m a x c)
dotM (Shell contra covar) (Shell contra' covar') =
  closeM (Shell contra' covar) $> Shell contra covar'

-- | composition of applicative boxes
dotA :: (Applicative f, Functor g) => Shell f g a x b -> Shell f g b x c -> g (Shell f g a x c)
dotA (Shell contra covar) (Shell contra' covar') = closeA (Shell contra' covar) $> Shell contra covar'

-- |
dotI :: (Functor g) => Shell Identity g a x b -> Shell Identity g b x c -> g (Shell Identity g a x c)
dotI (Shell contra covar) (Shell contra' covar') =
  closeI (Shell contra' covar) $> Shell contra covar'

-}

-- * CPS
-- https://github.com/robrix/focalized/blob/cc18df3aa6aec8d61b1d71a896a43ae598db2cbe/src/Focalized/Calculus.hs#L892-L973
