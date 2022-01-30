{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Stream where

import Prelude
import Control.Applicative
import Data.Bool
import Control.Monad
import Data.Function
import Data.Functor

newtype Fix f = Fix { unFix :: f (Fix f) }

-- The simplest, infinite stream
data Stream' a = Stream' a (Stream' a)
data StreamF a b = StreamF a b
type Stream a = Fix (StreamF a)

-- inspiration for pipes:
-- https://themonadreader.files.wordpress.com/2011/10/issue19.pdf
-- Proxy class from pipes
data Proxy' a' a b' b m r
    = Request a' (a  -> Proxy' a' a b' b m r )
    | Respond b  (b' -> Proxy' a' a b' b m r )
    | M          (m    (Proxy' a' a b' b m r))
    | Pure    r

data ProxyF a' a b' b m r f
    = RequestF a' (a  -> f)
    | RespondF b  (b' -> f)
    | MF          (m f)
    | PureF    r

type Proxy a' a b' b m r = Fix (ProxyF a' a b' b m r)


-- Simplest feedback loop. i is information being transmitted upstream.
--
-- from https://github.com/leonidas/codeblog/blob/master/2012/2012-01-08-streams-coroutines.md
newtype Coroutine' i o = Coroutine' { runC :: i -> (o, Coroutine' i o) }

newtype CoroutineF i o f = Coroutine (i -> (o,f))

type Coroutine i o = Fix (CoroutineF i o)



-- from https://rubenpieters.github.io/assets/papers/JFP20-pipes.pdf

data PipeCo' i o a = PipeCoIn' (i -> PipeCo' i o a) | PipeCoOut' o (PipeCo' i o a) | PipeCoReturn' a
data PipeCoF i o a f = PipeCoInF (i -> f) | PipeCoOutF o f | PipeCoReturnF a
type PipeCo i o a = Fix (PipeCoF i o a)

instance Functor (PipeCo' i o) where
  fmap f (PipeCoIn' a) = PipeCoIn' (fmap f . a)
  fmap f (PipeCoOut' o r) = PipeCoOut' o (fmap f r)
  fmap f (PipeCoReturn' a) = PipeCoReturn' (f a)

instance Applicative (PipeCo' i o) where
  pure = PipeCoReturn'
  (<*>) f (PipeCoIn' a) = PipeCoIn' (\i -> f <*> a i)
  (<*>) f (PipeCoOut' o a) = PipeCoOut' o (f <*> a)
  -- homomorphism
  (<*>) (PipeCoReturn' f) (PipeCoReturn' a) = PipeCoReturn' (f a)
  (<*>) (PipeCoIn' f) a = PipeCoIn' (\i -> f i <*> a)
  (<*>) (PipeCoOut' o f) a = PipeCoOut' o (f <*> a)

instance Monad (PipeCo' i o) where

  (PipeCoIn' h) >>= f = PipeCoIn' (h >=> f)
  (PipeCoOut' o r)>>= f = PipeCoOut' o (r >>=f)
  (PipeCoReturn' a) >>= f = f a

input :: PipeCo' i o i
input = PipeCoIn' PipeCoReturn'

output :: o -> PipeCo' i o ()
output o = PipeCoOut' o (PipeCoReturn' ())

return :: a -> PipeCo' i o a
return = PipeCoReturn'

doubler :: PipeCo' Int Int a
doubler = do
  i <- input
  output (i * 2)
  doubler

-- TODO: applicative version
doublerCo :: PipeCo' Int Int a
doublerCo = do
  i <- PipeCoIn' PipeCoReturn'
  PipeCoOut' (i * 2) (PipeCoReturn' ())
  doublerCo

doublerCoApp :: PipeCo' Int Int a
doublerCoApp =
  PipeCoOut' <$> fmap (2*) (PipeCoIn' PipeCoReturn') *> PipeCoReturn' () *> doublerCoApp

doublerCoF :: PipeCo' Int Int a
doublerCoF = undefined
  -- PipeCoOut' <$> fmap (2*) (PipeCoIn' PipeCoReturn') $> PipeCoReturn' () $> doublerCoApp

doublerCoFix :: PipeCo' Int Int a
doublerCoFix = fix $ \rec -> do
  i <- PipeCoIn' PipeCoReturn'
  PipeCoOut' (i * 2) (PipeCoReturn' ())
  rec

doublerCoAppFix :: PipeCo' Int Int a
doublerCoAppFix =
  fix $ \rec -> fmap (PipeCoOut' . (2*)) (PipeCoIn' PipeCoReturn') *> PipeCoReturn' () *> rec

-- Box methods
newtype Committer m a = Committer
  { commit :: a -> m Bool
  }

newtype Emitter m a = Emitter
  { emit :: m (Maybe a)
  }

data Box m a b = Box { committer :: Committer m a, emitter :: Emitter m b }

-- box as a sum type
data PipeB m a b = CommitterB (a -> m Bool) | EmitterB (m (Maybe a))

doubler' :: (Monad m, Num a) => Box m a a -> m ()
doubler' (Box c e) = go
  where
    go = do
      a <- emit e
      case a of
        Nothing -> pure ()
        Just a' ->
          do
            p <- commit c (2*a')
            bool (pure ()) go p

doublerMaybe :: PipeCo' Int Int ()
doublerMaybe = do
  i <- input'
  case i of
    Nothing -> return'
    Just a -> do
      p <- output' (2*a)
      bool return' doublerMaybe p

-- experiment - specilialize to maybe
input' :: PipeCo' i o (Maybe i)
input' = PipeCoIn' (PipeCoReturn' . Just)

output' :: o -> PipeCo' i o Bool
output' o = PipeCoOut' o (PipeCoReturn' True)

return' :: PipeCo' i o ()
return' = PipeCoReturn' ()

-- from streaming
data Streaming' f m r =
  Step !(f (Streaming' f m r)) |
  Effect (m (Streaming' f m r)) |
  ReturnS r

data StreamingF f m r n
  = StepF !(f n)
  | EffectF (m n)
  | ReturnSF r

type Streaming f m r = Fix (StreamingF f m r)

-- end
