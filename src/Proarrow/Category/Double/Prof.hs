{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Double.Prof where

import Data.Kind (Type, Constraint)
import Data.Function (($))
import Data.Proxy (Proxy(..))

import Proarrow.Category.Bicategory (Path(..), type (+++), BICAT, Bicategory (..))
import Proarrow.Core (PRO, CategoryOf(..), Profunctor(..), (:~>), CAT, Promonad (..), dimapDefault, lmap, rmap)
import Proarrow.Category.Double (DOUBLE, Double (..))
import Proarrow.Profunctor.Composition ((:.:) (..))


newtype ProfK j k = PK (j -> k -> Type)

type ProfList :: Path ProfK j k -> PRO j k
data ProfList ps a b where
  ProfNil :: CategoryOf k => (a :: k) ~> b -> ProfList Nil a b
  ProfCons :: Profunctor p => p a b -> ProfList ps b c -> ProfList (PK p ::: ps) a c

instance (CategoryOf j, CategoryOf k) => Profunctor (ProfList ps :: PRO j k) where
  dimap l r (ProfNil f) = ProfNil (dimap l r f)
  dimap l r (ProfCons p ps) = ProfCons (lmap l p) (rmap r ps)
  r \\ ProfNil f = r \\ f
  r \\ ProfCons p ps = r \\ p \\ ps

pappend :: (CategoryOf i, CategoryOf j, CategoryOf k) => ProfList ps (a :: i) (b :: j) -> ProfList qs b (c :: k) -> ProfList (ps +++ qs) a c
pappend (ProfNil f) qs = lmap f qs
pappend (ProfCons p ps) qs = ProfCons p (pappend ps qs)

type PSplit :: forall {i} {j}. Path ProfK i j -> Constraint
class PSplit (ps :: Path ProfK i j) where
  psplit
    :: forall {k} (qs :: Path ProfK j k) a c r
    . (CategoryOf i, CategoryOf j, CategoryOf k)
    => (forall (b :: j). ProfList ps (a :: i) b -> ProfList qs b (c :: k) -> r)
    -> ProfList (ps +++ qs) a c -> r
  withAppendPSplit' :: PSplit qs => proxy qs -> (PSplit (ps +++ qs) => r) -> r
instance PSplit Nil where
  psplit k qs = k (ProfNil id) qs \\ qs
  withAppendPSplit' _ r = r
instance PSplit ps => PSplit (PK p ::: ps) where
  psplit k (ProfCons p pqs) = psplit @ps (k . ProfCons p) pqs
  withAppendPSplit' = withAppendPSplit' @ps

withAppendPSplit :: forall ps qs r. (PSplit ps, PSplit qs) => (PSplit (ps +++ qs) => r) -> r
withAppendPSplit = withAppendPSplit' @ps (Proxy @qs)


type ProfSq :: DOUBLE ProfK ProfK
data ProfSq ps qs fs gs where
  ProfSq
    :: forall {h} {i} {j} {k} ps qs fs gs
     . (CategoryOf h, CategoryOf i, CategoryOf j, CategoryOf k, PSplit ps, PSplit qs, PSplit fs, PSplit gs)
    => ProfList ps :.: ProfList gs :~> ProfList fs :.: ProfList qs
    -> ProfSq (ps :: Path ProfK h i) (qs :: Path ProfK j k) fs gs

type Biprof :: BICAT ProfK
data Biprof ps qs where
  Biprof
    :: forall {j} {k} (ps :: Path ProfK j k) qs
     . (CategoryOf j, CategoryOf k, PSplit ps, PSplit qs)
    => ProfList ps :~> ProfList qs
    -> Biprof ps qs
instance (CategoryOf j, CategoryOf k) => Profunctor (Biprof :: CAT (Path ProfK j k)) where
  dimap = dimapDefault
  r \\ Biprof{} = r
instance (CategoryOf j, CategoryOf k) => Promonad (Biprof :: CAT (Path ProfK j k)) where
  id = Biprof id
  Biprof n . Biprof m = Biprof (n . m)
instance (CategoryOf j, CategoryOf k) => CategoryOf (Path ProfK j k) where
  type (~>) = Biprof
  type Ob (ps :: Path ProfK j k) = (PSplit ps, CategoryOf j, CategoryOf k)

-- | The bicategory of profunctors.
instance Bicategory ProfK where
  type BiOb ProfK k = CategoryOf k
  Biprof @as @bs n `o` Biprof @cs @ds m = withAppendPSplit @as @cs $ withAppendPSplit @bs @ds $
    Biprof $ psplit (\as cs -> pappend (n as) (m cs))
  r \\\ Biprof{} = r

-- | The double category of profunctors.
instance Double ProfK ProfK where
  type Sq ProfK ProfK = ProfSq
  object = ProfSq id
  hId = ProfSq \(ps :.: ProfNil f) -> ProfNil id :.: rmap f ps \\ ps
  ProfSq @_ @_ @fs @gs n ||| ProfSq @_ @_ @hs @is m = withAppendPSplit @gs @is $ withAppendPSplit @fs @hs $ ProfSq \(ps :.: gis) ->
    psplit
      (\gs is -> case n (ps :.: gs) of
        fs :.: qs -> case m (qs :.: is) of
          hs :.: rs -> pappend fs hs :.: rs)
      gis
  vId = ProfSq \(ProfNil f :.: ps) -> lmap f ps :.: ProfNil id \\ ps
  ProfSq @ps @qs n === ProfSq @rs @ss m = withAppendPSplit @ps @rs $ withAppendPSplit @qs @ss $ ProfSq \(prs :.: hs) ->
    psplit
      (\ps rs -> case m (rs :.: hs) of
        gs :.: ss -> case n (ps :.: gs) of
          fs :.: qs -> fs :.: pappend qs ss)
    prs
