{-# LANGUAGE AllowAmbiguousTypes #-}

-- | The category __freely generated__ by a quiver @p@: an arrow is a finite path of generators
-- ('PCons' onto 'PNil'), and an object is simply a vertex.
--
-- This is "Proarrow.Category.Instance.Free" without the structure list. Structures introduce new
-- objects (a formal product, a formal exponential), which is why the free /structured/ category has
-- to give its objects a shape of their own and ask only
-- @'Proarrow.Category.Instance.Free.IsFreeOb'@ of them. With no structures there is nothing new to
-- form, so the objects here can be the vertices themselves and 'Ob' is inherited from the base kind.
-- That is the difference that matters: an object of @'PATHS' p@ can be taken apart by whatever the
-- base kind's 'Ob' provides, and an object of the free structured category cannot, because
-- @Lower@\/@lowerOb@ folds a shape into another category's /object/ and never yields a value
-- indexed by that shape.
--
-- Setting the structure list to @'[]@ is not a substitute either:
-- @'Proarrow.Category.Instance.Free.St'@ carries its @HasStructure@ dictionary as a given, and the
-- absence of an instance at @'[]@ is not absurdity the pattern checker can use, so every consumer
-- would carry an unreachable branch.
--
-- __Equations__ are supported, by 'Rewrite'. Composition only ever adds an arrow at the outermost
-- end of the spine, so a quiver can normalise each new arrow against an already-normal path and
-- keep every value in normal form. Leave 'rewrite' at its default and the category is free.
--
-- The base kind must be a category because 'foldPaths' interprets along a functor out of it, and
-- functors between kinds are written as representable profunctors here. Its arrows are never used,
-- so the intended base is a discrete one, where a functor is just a map of vertices.
module Proarrow.Category.Instance.Paths where

import Data.Type.Equality ((:~:) (..))
import Prelude (Eq (..), Maybe (..), Show (..), showParen, showString)
import Prelude qualified as P

import Proarrow.Category.Enriched.Thin
  ( AtOb (..)
  , Enumerable (..)
  , Finite (..)
  , FmapWrap
  , Indexed (..)
  , MapWrap
  , withWrapAtLookup
  , wrapFinite
  )
import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Profunctor (..)
  , Promonad (..)
  , Show2
  , UN
  , WrappedOb
  , dimapDefault
  , type (+->)
  )
import Proarrow.Profunctor.Representable (Representable (..))

-- | The objects of the free category on @p@: its vertices.
type data PATHS (p :: CAT k) = PTH k

-- | A path of generators, as a right-associated spine, which is what makes the category laws hold
-- definitionally.
type Paths :: CAT (PATHS p)
data Paths a b where
  PNil :: (Ob a) => Paths (PTH a) (PTH a)
  PCons :: (Ob a, Ob b) => p a b -> Paths (i :: PATHS p) (PTH a) -> Paths i (PTH b)

-- | The equations of the generated category, as a rewriting system on paths. 'rewrite' is handed a
-- generator and the already-normalised path it is being composed onto, and returns the normal form
-- of the two together; the default keeps the path as it is, which generates the free category.
--
-- An equation is one clause. For @Secr ⨟ WorksIn = id@, match the junction and drop both arrows:
--
-- > rewrite WorksIn (PCons Secr more) = more
--
-- The whole tail is in scope, so a longer left-hand side can be matched, and recursing on the
-- result renormalises a junction the rewrite has just exposed.
--
-- __Confluence and termination are the caller's to establish.__ Nothing here checks them, and a
-- system that lacks them breaks associativity of composition silently. Two further obligations come
-- with any non-default instance: 'foldPaths' is a functor only for interpretations that respect the
-- equations, and so is any other consumer that matches on generators.
class Rewrite (p :: CAT k) where
  rewrite :: (Ob a, Ob b) => p a b -> Paths (i :: PATHS p) (PTH a) -> Paths i (PTH b)
  rewrite = PCons

-- | Decidable equality of generators, which also has to decide their sources: the object between
-- two arrows of a path is existential, so @'Eq' (p x y)@ alone cannot compare two spines. (This is
-- why 'Proarrow.Core.Eq2' does not serve: that is equality of arrows of a fixed category, which is
-- what 'Proarrow.Limit.Pullback.isMono' wants.)
class EqGen (p :: CAT k) where
  eqGen :: p x b -> p y b -> Maybe (x :~: y)

-- | Structural equality of paths. This is equality of arrows exactly when 'rewrite' is confluent
-- and every path was built through 'emb', 'id' and composition, which keep paths in normal form.
-- The free /structured/ category cannot offer this: there, equality has to be decided by folding
-- both sides into some category that identifies them.
instance (EqGen p) => Eq (Paths (a :: PATHS p) b) where
  PNil == PNil = P.True
  PCons q f == PCons q' g = case eqGen q q' of
    Just Refl -> f == g
    Nothing -> P.False
  _ == _ = P.False

instance (Show2 p) => Show (Paths (a :: PATHS p) b) where
  showsPrec _ PNil = showString "id"
  showsPrec d (PCons q PNil) = showsPrec d q
  showsPrec d (PCons q f) = showParen (d P.> 9) (showsPrec 10 q . showString " . " . showsPrec 10 f)

-- | How many generators a path is made of. With a non-default 'rewrite' this is a way to see that
-- an equation fired, since a path that reduces comes out shorter.
pathLength :: Paths a b -> P.Int
pathLength PNil = 0
pathLength (PCons _ f) = 1 P.+ pathLength f

-- | A single generator, normalised. Named as in "Proarrow.Category.Instance.Free".
emb :: (Ob a, Ob b, Rewrite p) => p a b -> (PTH a :: PATHS p) ~> PTH b
emb q = rewrite q PNil

-- | Interpret a path in any category, given an interpretation of the generators between the images
-- of their endpoints: the universal property of the free category. A functor out of @'PATHS' p@ is
-- exactly a map of vertices together with such an interpretation, with nothing to check, because a
-- quiver has no composition to preserve.
--
-- The first argument supplies @'Ob'@ for an image object. It has to be passed in rather than taken
-- from @f@ by 'Proarrow.Profunctor.Representable.withObRep', because the usual caller is the very
-- functor being defined: recovering the evidence from @f@ would run @f@\'s own 'fmap' on the empty
-- path and loop. Where the target's objects are unconstrained the witness is just @\\r -> r@.
foldPaths
  :: forall {k} {k'} {p :: CAT k} (f :: PATHS p +-> k') a b
   . (Representable f)
  => (forall x r. (Ob x) => ((Ob (f % PTH x)) => r) -> r)
  -> (forall x y. (Ob x, Ob y) => p x y -> (f % PTH x) ~> (f % PTH y))
  -> (PTH a :: PATHS p) ~> PTH b
  -> (f % PTH a) ~> (f % PTH b)
foldPaths withObF pn = go
  where
    go :: forall x y. (PTH x :: PATHS p) ~> PTH y -> (f % PTH x) ~> (f % PTH y)
    go PNil = withObF @x id
    go (PCons q g) = pn q . go g

instance (CategoryOf k, Rewrite p) => CategoryOf (PATHS (p :: CAT k)) where
  type (~>) = Paths
  type Ob a = WrappedOb PTH a

-- | Objects are vertices, so a free category has exactly as many of them as its quiver has, however
-- many arrows the paths add -- and unboundedly many is the normal case. So a free category is
-- 'Finite' without being anywhere near thin or decidable. What they buy is enumeration of the
-- /objects/ alone -- enough for @Proarrow.Testing.genSomeFinite@ to derive a schema\'s object
-- palette, and not enough for anything that wants to enumerate arrows.
instance (Indexed k) => Indexed (PATHS (p :: CAT k)) where
  type Index (a :: PATHS p) = Index (UN PTH a)
  type At (PATHS (p :: CAT k)) i = FmapWrap PTH (At k i)

instance (Finite k) => Finite (PATHS (p :: CAT k)) where
  type Objects (PATHS (p :: CAT k)) = MapWrap PTH (Objects k)
  finite = wrapFinite @PTH
  withAtLookup = withWrapAtLookup @PTH

instance (Enumerable k, Rewrite p) => Enumerable (PATHS (p :: CAT k)) where
  withIndex @(PTH a) r = withIndex @k @a r
  atOb i = case atOb @k i of
    AtJust -> AtJust
    AtNothing -> AtNothing

instance (CategoryOf k, Rewrite p) => Promonad (Paths :: CAT (PATHS (p :: CAT k))) where
  id = PNil
  PNil . g = g
  PCons q f . g = rewrite q (f . g)

instance (CategoryOf k, Rewrite p) => Profunctor (Paths :: CAT (PATHS (p :: CAT k))) where
  dimap = dimapDefault
  r \\ PNil = r
  r \\ PCons _ f = r \\ f
