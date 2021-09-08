{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Tristero
  (
  )
where

import Prelude
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

{-

Main references:
--

[Essence of AD](http://conal.net/papers/essence-of-ad/)

[Deconstructing Lambdas—An Awkward Guide to Programming Without Functions](https://www.youtube.com/watch?v=xZmPuz9m2t0)

[What You Needa Know about Yoneda](https://dl.acm.org/doi/pdf/10.1145/3236779)

[profunctor optics](http://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/poptics.pdf)


Supplementary
---
[The Dao](https://github.com/BartoszMilewski/Publications/blob/master/TheDaoOfFP/1-CleanSlate.pdf)

[Arrows, like Monads, are Monoids](https://www.pure.ed.ac.uk/ws/portalfiles/portal/22099462/http//www.haskell.org/arrow.pdf)

[Compiling to Categories](http://conal.net/papers/compiling-to-categories/)

[A tutorial on the universality and expressiveness of fold](https://www.cs.nott.ac.uk/~pszgmh/fold.pdf)


[Semirings and Formal Power Series](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.304.6152&rep=rep1&type=pdf)


Libraries
---

[semiring-num](https://hackage.haskell.org/package/semiring-num-1.6.0.4/docs/Data-Semiring-Numeric.html)

Typeclasses versus free construction.
---

freer

Delimiting
---

https://ix.cs.uoregon.edu/~pdownen/publications/delimited-control-effects.pdf


Convolution
---

[FUNCTIONAL PEARLS Power Series, Power Serious](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.333.3156&rep=rep1&type=pdf)

From https://doisinkidney.com/posts/2017-10-13-convolutions-and-semirings.html

if you want a list like this: [(y,x-y) | x <- [0..], y <- [0..x] ]
[(0,0),(0,1),(1,0),(0,2),(1,1),(2,0),(0,3),(1,2),(2,1),(3,0)...

Then what you’re looking for is a convolution like:

https://byorgey.wordpress.com/2008/04/22/list-convolutions/

https://arxiv.org/pdf/1903.10677.pdf

Search
--

[A\lbegras for combinatorial search](https://sci-hub.ee/10.1017/S0956796809007321)

[backtracjking](http://okmij.org/ftp/Computation/LogicT.pdf)


Line-by-line check
---

[Generalized Convolution and Efficient Language Recognition](https://arxiv.org/pdf/1903.10677.pdf)

Nice Monoid symbols

CT basics

https://ruor.uottawa.ca/bitstream/10393/36118/3/Khan_Sakif_2017_thesis.pdf


take 1
---

- we can get a kleisli category from a monad
- this kleilsli category has structure that corresponds to the structure of the monad
- arrows have a kind of kleisli category associated with them, "freyd category"
- they also have the same correspondence, the structure of an arrow (or the underlying profunctor) determines the structure of the kleisli category.

- 'Arrow' is Free (Coyoneda (Profunctor))
- The free profunctor is FreeA(Coyoneda(ProfExpr)) (over ProfExpr)
- ProfExpr : (p : Type->Type->Type) -> (a:Type) -> (b:Type) -> Type (needs a GADT)
- universal arrow: if you define a data structure, then *any* function on that data structure can be done using a fold. But if the data structure contains contravariance, you can't use foldr/recursion schemes. A fold (aka catamorphism) is a universal way to deconstruct something and use it in computation, but foldr only works on bifunctorial, covariant patterns.

take 2

So the way we construct a freer monad is by starting with a GADT for the syntax, which has type

Expr : (f:Type->Type) -> (a:Type) -> Type

then we wrap it with "free functor/coyoneda"

Coyoneda :: (b -> a) -> f b -> Coyoneda f a

and then we wrap that with the free monoid in the category of endofunctors, ie a free monad

so Free(Coyoneda(Expr)) gives us the free monad over Expr.

Now, the same thing can be made analogously for profunctors. The key step is that we need a GADT that has both a covariant and contravariant argument

ProfExpr : (p : Type->Type->Type) -> (a:Type) -> (b:Type) -> Type

then we wrap this with the 'profunctor yoneda'

data Coyoneda p a b where
  Coyoneda :: (a -> x) -> (y -> b) -> p x y -> Coyoneda p a b

which gives us the 'free profunctor'

and all we need to do after that is wrap this with 'the free monoid in the category of profunctors', ie the free arrow

FreeA(Coyoneda(ProfExpr))

eg. so a closure/fold over FreeA(Coyoneda(ProfExpr)) will give us "operational arrows"

-}

module Egg where

import Prelude
import Data.Profunctor
import Data.Bifunctor
import Data.Function

data Adapter a b s t = Adapter { from :: s → a, to :: b → t }

instance Profunctor (Adapter a b) where
  dimap f g (Adapter o i) = Adapter (o . f) (g . i)

newtype State s a = State { run :: s → (a,s) }

instance Functor (State s) where
  fmap f (State s) = State $ first f . s

instance Applicative (State s) where
  pure a = State (a,)
  (State f) <*> (State a) = State $ (\(a',(f',s')) -> (f' a',s')) . second f . a

type Thing d p a b s t = p a b `d` p s t

type Optic p a b s t = Thing (->) p a b s t

type AdapterP a b s t = ∀ p. Profunctor p ⇒ Optic p a b s t

class Profunctor p ⇒ Cartesian p where
  first' :: p a b → p (a, c) (b, c)
  second' :: p a b → p (c, a) (c, b)

class Profunctor p ⇒ Cocartesian p where
  left :: p a b → p (Either a c) (Either b c)
  right :: p a b → p (Either c a) (Either c b)

class Profunctor p ⇒ Monoidal p where
  par :: p a b → p c d → p (Either a c) (Either b d)
  empty :: p () ()

type LensP a b s t = ∀p . Cartesian p ⇒ Optic p a b s t

data Lens a b s t = Lens {view :: s → a, update :: (b, s) → t}

instance Profunctor (Lens a b) where
  dimap f g (Lens v u) = Lens (v . f) (g . u . cross id f)

instance Cartesian (Lens a b) where
  first' (Lens v u) = Lens (v . fst) (fork (u . cross id fst) (snd . snd))
  second' (Lens v u) = Lens (v . snd) (fork (fst . snd) (u . cross id snd))

fork :: (t -> a) -> (t -> b) -> t -> (a, b)
fork f g x = (f x, g x)

cross :: (t1 -> a) -> (t2 -> b) -> (t1, t2) -> (a, b)
cross f g (x, y) = (f x, g y)

data Prism a b s t = Prism {match :: s → Either t a, build :: b → t}

type PrismP a b s t = ∀p . Cocartesian p ⇒ Optic p a b s t

instance Profunctor (Prism a b) where
  dimap f g (Prism m b) = Prism (plus g id . m . f) (g . b)

instance Cocartesian (Prism a b) where
  left (Prism m b) = Prism (either (plus Left id . m) (Left . Right)) (Left . b)
  right (Prism m b) = Prism (either (Left . Left) (plus Right id . m)) (Right . b)

plus :: (t1 -> a) -> (t2 -> b) -> Either t1 t2 -> Either a b
plus f _ (Left x) = Left (f x)
plus _ g (Right y) = Right (g y)

newtype Traversal a b s t = Traversal {extract :: s → FunList a b t}

data FunList a b t = Done t | More a (FunList a b (b → t))

instance Functor (FunList a b) where
  fmap f (Done t) = Done (f t)
  fmap f (More x l) = More x (fmap (f .) l)

instance Applicative (FunList a b) where
  pure = Done
  (Done f) <*> l  = fmap f l
  (More x l) <*> l' = More x (fmap flip l <*> l')

type TraversalP a b s t =
  ∀ p.
  (Cartesian p,Cocartesian p,Monoidal p) ⇒
  Optic p a b s t

instance Profunctor (Traversal a b) where
  dimap f g (Traversal h) = Traversal (fmap g . h . f)

instance Cartesian (Traversal a b) where
  first' (Traversal h) = Traversal (\(s,c) -> fmap (,c) (h s))
  second' (Traversal h) = Traversal (\(c,s) -> fmap (c,) (h s))

instance Cocartesian (Traversal a b) where
  left (Traversal h) = Traversal (either (fmap Left . h) (Done . Right))
  right (Traversal h) = Traversal (either (Done . Left) (fmap Right . h))

instance Monoidal (Traversal a b) where
  par (Traversal h) (Traversal k) = Traversal undefined -- (h,k)
  empty = Traversal pure

newtype UpStar f a b = UpStar { unUpStar:: a -> f b}

instance Functor f ⇒ Profunctor (UpStar f) where
  dimap f g (UpStar h) = UpStar (fmap g . h . f)

instance Functor f => Cartesian (UpStar f) where
  first' (UpStar f) = UpStar (rstrength . cross f id)
  second' (UpStar f) = UpStar (lstrength . cross id f)

rstrength :: Functor f ⇒ (f a, b) → f (a, b)
rstrength (fx, y) = fmap (,y) fx

lstrength :: Functor f ⇒ (a, f b) → f (a, b)
lstrength (x, fy) = fmap (x,) fy

instance Applicative f ⇒ Cocartesian (UpStar f) where
  left (UpStar f) = UpStar (either (fmap Left . f) (pure . Right))
  right (UpStar f) = UpStar (either (pure . Left) (fmap Right . f))

instance Applicative f ⇒ Monoidal (UpStar f) where
  empty = UpStar pure
  par h k = undefined -- UpStar (pair (unUpStar h) (unUpStar k))

pair :: Applicative f ⇒ (a → f b) → (c → f d) → (a,c) → f (b, d)
pair h k (x, y) = (,) <$> h x <*> k y

traverseOf :: TraversalP a b s t -> (∀ f. Applicative f ⇒ (a -> f b) -> s -> f t)
traverseOf p f = unUpStar (p (UpStar f))
