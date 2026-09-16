-- | The __opposite category__: the kind @'OPPOSITE' k@ wraps @k@ in 'OP', and an arrow
-- @'OP' a '~>' 'OP' b@ is an arrow @b '~>' a@ of @k@. 'Op' (and its inverse 'UnOp') also flips
-- profunctors, swapping their two arguments -- the prototypical use of a newtype wrapper on a kind
-- to give one collection of types a second category structure.
module Proarrow.Category.Instance.Opposite where

import Data.Type.Nat (snat)

import Proarrow.Category.Enriched.Thin
  ( AtOb (..)
  , DecidableProfunctor (..)
  , Enumerable (..)
  , Finite (..)
  , FmapWrap
  , Indexed (..)
  , MapWrap
  , Thin
  , ThinProfunctor (..)
  , atOb
  , mapDecision
  , withWrapAtLookup
  , wrapFinite
  )
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), UN, WrappedOb, lmap, type (+->))
import Proarrow.Functor (Functor (..))

newtype OPPOSITE k = OP k

-- | Flips the two arguments of a profunctor, giving a profunctor between the 'OPPOSITE'
-- categories; at @p = ('~>')@ this is the hom of the opposite category.
type Op :: j +-> k -> OPPOSITE k +-> OPPOSITE j
data Op p a b where
  Op :: {unOp :: p b a} -> Op p (OP a) (OP b)

instance (Profunctor p) => Functor (Op p a) where
  map (Op f) (Op p) = Op (lmap f p)

instance (Profunctor p) => Profunctor (Op p) where
  dimap (Op l) (Op r) = Op . dimap r l . unOp
  r \\ Op f = r \\ f

instance Functor Op where
  map (Prof n) = Prof \(Op p) -> Op (n p)

-- | The opposite category of the category of `k`.
instance (CategoryOf k) => CategoryOf (OPPOSITE k) where
  type (~>) = Op (~>)
  type Ob a = WrappedOb OP a

instance (Promonad c) => Promonad (Op c) where
  id = Op id
  Op f . Op g = Op (g . f)

instance (ThinProfunctor p) => ThinProfunctor (Op p) where
  type HasArrow (Op p) (OP a) (OP b) = HasArrow p b a
  arr = Op arr
  withArr (Op f) r = withArr f r

instance (DecidableProfunctor p) => DecidableProfunctor (Op p) where
  type Holds (Op p) (OP a) (OP b) = Holds p b a
  decide @(OP a) @(OP b) = mapDecision Op (decide @p @b @a)
  toHolds (Op f) r = toHolds f r

-- | Inverse to 'Op': unwraps a profunctor between 'OPPOSITE' categories to one between the
-- underlying kinds.
type UnOp :: OPPOSITE k +-> OPPOSITE j -> j +-> k
data UnOp p a b where
  UnOp :: {unUnOp :: p (OP b) (OP a)} -> UnOp p a b

instance (CategoryOf j, CategoryOf k, Profunctor p) => Profunctor (UnOp p :: j +-> k) where
  dimap l r = UnOp . dimap (Op r) (Op l) . unUnOp
  r \\ UnOp f = r \\ f

instance (Thin j, Thin k, ThinProfunctor p) => ThinProfunctor (UnOp p :: j +-> k) where
  type HasArrow (UnOp p) a b = HasArrow p (OP b) (OP a)
  arr = unOp arr
  withArr f r = withArr (Op f) r

instance (Thin j, Thin k, DecidableProfunctor p) => DecidableProfunctor (UnOp p :: j +-> k) where
  type Holds (UnOp p) a b = Holds p (OP b) (OP a)
  decide @a @b = mapDecision UnOp (decide @p @(OP b) @(OP a))
  toHolds (UnOp f) r = toHolds f r

-- | The opposite category has the same objects, numbered the same way.
instance (Indexed k) => Indexed (OPPOSITE k) where
  type Index (a :: OPPOSITE k) = Index (UN OP a)
  type At (OPPOSITE k) i = FmapWrap OP (At k i)

instance (Finite k) => Finite (OPPOSITE k) where
  type Objects (OPPOSITE k) = MapWrap OP (Objects k)
  finite = wrapFinite @OP
  withAtLookup = withWrapAtLookup @OP

instance (Enumerable k) => Enumerable (OPPOSITE k) where
  withIndex @(OP a) r = withIndex @k @a r
  withOb @a r = case atOb @k (snat @(Index a)) of AtJust -> r
  atOb i = case atOb @k i of
    AtJust -> AtJust
    AtNothing -> AtNothing
