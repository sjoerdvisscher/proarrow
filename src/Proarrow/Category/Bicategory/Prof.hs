{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Bicategory.Prof where

import Data.Kind (Constraint, Type)
import Data.Function (($))

import Proarrow.Category.Bicategory (type Path(..), type (+++), BICAT, Bicategory (..), SPath(..), IsPath(..), isPathAppend)
import Proarrow.Core (PRO, CategoryOf(..), Profunctor(..), (:~>), CAT, Promonad (..), dimapDefault, lmap, rmap, UN, Is)
import Proarrow.Profunctor.Representable (Representable)
import Proarrow.Profunctor.Corepresentable (Corepresentable)
import Proarrow.Category.Instance.Prof ()


newtype ProfK (cl :: Type) j k = PK (PRO j k)
type instance UN PK (PK p) = p

data ProfC
data ProfRepC
data ProfCorepC

type family ProfConstraint (cl :: Type) (p :: PRO j k) :: Constraint
type instance ProfConstraint ProfC p = Profunctor p
type instance ProfConstraint ProfRepC p = Representable p
type instance ProfConstraint ProfCorepC p = Corepresentable p

type ProfList :: forall cl -> Path (ProfK cl) j k -> PRO j k
data ProfList cl ps a b where
  ProfNil :: forall {k} (a :: k) b cl. CategoryOf k => a ~> b -> ProfList cl Nil a b
  ProfCons :: forall p cl ps f a b c. (Profunctor p, ProfConstraint cl p, Is PK f, p ~ UN PK f) => p a b -> ProfList cl ps b c -> ProfList cl (f ::: ps) a c

instance (CategoryOf j, CategoryOf k) => Profunctor (ProfList cl ps :: PRO j k) where
  dimap l r (ProfNil f) = ProfNil (dimap l r f)
  dimap l r (ProfCons p ps) = ProfCons (lmap l p) (rmap r ps)
  r \\ ProfNil f = r \\ f
  r \\ ProfCons p ps = r \\ p \\ ps

pappend :: (CategoryOf i, CategoryOf j, CategoryOf k) => ProfList cl ps (a :: i) (b :: j) -> ProfList cl qs b (c :: k) -> ProfList cl (ps +++ qs) a c
pappend (ProfNil f) qs = lmap f qs
pappend (ProfCons p ps) qs = ProfCons p (pappend ps qs)

psplit
  :: (CategoryOf i, CategoryOf j, CategoryOf k, IsPath ps)
  => (forall (b :: j). ProfList cl ps (a :: i) b -> ProfList cl qs b (c :: k) -> r)
  -> ProfList cl (ps +++ qs) a c -> r
psplit = go singPath
  where
    go :: CategoryOf k => SPath ps
       -> (forall (b :: j). ProfList cl ps (a :: i) b -> ProfList cl qs b (c :: k) -> r)
       -> ProfList cl (ps +++ qs) a c -> r
    go SNil k qs = k (ProfNil id) qs \\ qs
    go (SCons ps) k (ProfCons p pqs) = go ps (k . ProfCons p) pqs


type Biprof :: BICAT (ProfK cl)
data Biprof ps qs where
  Biprof
    :: forall {j} {k} {cl} (ps :: Path (ProfK cl) j k) qs
     . (CategoryOf j, CategoryOf k, Ob ps, Ob qs)
    => ProfList cl ps :~> ProfList cl qs
    -> Biprof ps qs
instance (CategoryOf j, CategoryOf k) => Profunctor (Biprof :: CAT (Path (ProfK cl) j k)) where
  dimap = dimapDefault
  r \\ Biprof{} = r
instance (CategoryOf j, CategoryOf k) => Promonad (Biprof :: CAT (Path (ProfK cl) j k)) where
  id = Biprof id
  Biprof n . Biprof m = Biprof (n . m)
instance (CategoryOf j, CategoryOf k) => CategoryOf (Path (ProfK cl) j k) where
  type (~>) = Biprof
  type Ob ps = IsPath ps

-- | The bicategory of categories, profunctors and natural transformations.
instance Bicategory (ProfK cl) where
  type Ob0 (ProfK cl) k = CategoryOf k
  type Ob1 (ProfK cl) p = (Is PK p, ProfConstraint cl (UN PK p))
  Biprof @as @bs n `o` Biprof @cs @ds m = isPathAppend @as @cs $ isPathAppend @bs @ds $
    Biprof $ psplit (\as cs -> pappend (n as) (m cs))
  r \\\ Biprof{} = r
  -- fromList Nil = Biprof \(ProfNil f) -> ProfNil f
  -- fromList (Cons (Prof n) ns) = case fromList ns of Biprof f -> Biprof \(ProfCons p ps) -> ProfCons (n p) (f ps)


-- type Prof :: CAT (ProfK cl j k)
-- data Prof p q where
--   Prof :: (ProfConstraint cl p, Profunctor p, ProfConstraint cl q, Profunctor q) => p :~> q -> Prof (PK p :: ProfK cl j k) (PK q)

-- instance Profunctor Prof where
--   dimap = dimapDefault
--   r \\ Prof n = r \\ n
-- instance Promonad Prof where
--   id = Prof id
--   Prof m . Prof n = Prof (m . n)
-- instance CategoryOf (ProfK cl j k) where
--   type (~>) = Prof
--   type Ob @(ProfK cl j k) p = (Is PK p, Profunctor (UN PK p), ProfConstraint cl (UN PK p))
