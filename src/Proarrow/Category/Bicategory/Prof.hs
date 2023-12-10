{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Bicategory.Prof where

import Data.Kind (Constraint, Type)
import Data.Function (($))
import Data.Proxy (Proxy(..))

import Proarrow.Category.Bicategory (Path(..), type (+++), BICAT, Bicategory (..))
import Proarrow.Core (PRO, CategoryOf(..), Profunctor(..), (:~>), CAT, Promonad (..), dimapDefault, lmap, rmap, UN, Is)
import Proarrow.Profunctor.Representable (Representable)
import Proarrow.Profunctor.Corepresentable (Corepresentable)


newtype ProfK (cl :: Type) j k = PK (PRO j k)
type instance UN PK (PK p) = p

data ProfC
data ProfRepC
data ProfCorepC

type family ProfConstraint (cl :: Type) (p :: PRO j k) :: Constraint
type instance ProfConstraint ProfC p = Profunctor p
type instance ProfConstraint ProfRepC p = Representable p
type instance ProfConstraint ProfCorepC p = Corepresentable p

type ProfList :: Type -> Path (ProfK cl) j k -> PRO j k
data ProfList cl ps a b where
  ProfNil :: forall {k} (a :: k) b cl. CategoryOf k => a ~> b -> ProfList cl Nil a b
  ProfCons :: (Profunctor p, ProfConstraint cl p, Is PK f, p ~ UN PK f) => p a b -> ProfList cl ps b c -> ProfList cl (f ::: ps) a c

instance (CategoryOf j, CategoryOf k) => Profunctor (ProfList cl ps :: PRO j k) where
  dimap l r (ProfNil f) = ProfNil (dimap l r f)
  dimap l r (ProfCons p ps) = ProfCons (lmap l p) (rmap r ps)
  r \\ ProfNil f = r \\ f
  r \\ ProfCons p ps = r \\ p \\ ps

pappend :: (CategoryOf i, CategoryOf j, CategoryOf k) => ProfList cl ps (a :: i) (b :: j) -> ProfList cl qs b (c :: k) -> ProfList cl (ps +++ qs) a c
pappend (ProfNil f) qs = lmap f qs
pappend (ProfCons p ps) qs = ProfCons p (pappend ps qs)

type PSplit :: forall {i} {j} {cl}. Path (ProfK cl) i j -> Constraint
class PSplit (ps :: Path (ProfK cl) i j) where
  psplit
    :: forall {k} (qs :: Path (ProfK cl) j k) a c r
    . (CategoryOf i, CategoryOf j, CategoryOf k)
    => (forall (b :: j). ProfList cl ps (a :: i) b -> ProfList cl qs b (c :: k) -> r)
    -> ProfList cl (ps +++ qs) a c -> r
  withAppendPSplit' :: PSplit qs => proxy qs -> (PSplit (ps +++ qs) => r) -> r
instance PSplit Nil where
  psplit k qs = k (ProfNil id) qs \\ qs
  withAppendPSplit' _ r = r
instance (PSplit ps, Is PK f, p ~ UN PK f) => PSplit (f ::: ps) where
  psplit k (ProfCons p pqs) = psplit @ps (k . ProfCons p) pqs
  withAppendPSplit' = withAppendPSplit' @ps

withAppendPSplit :: forall ps qs r. (PSplit ps, PSplit qs) => (PSplit (ps +++ qs) => r) -> r
withAppendPSplit = withAppendPSplit' @ps (Proxy @qs)

type Biprof :: BICAT (ProfK cl)
data Biprof ps qs where
  Biprof
    :: forall {j} {k} {cl} (ps :: Path (ProfK cl) j k) qs
     . (CategoryOf j, CategoryOf k, PSplit ps, PSplit qs)
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
  type Ob (ps :: Path (ProfK cl) j k) = (PSplit ps, CategoryOf j, CategoryOf k)

-- | The bicategory of profunctors.
instance Bicategory (ProfK cl) where
  type BiOb (ProfK cl) k = CategoryOf k
  Biprof @as @bs n `o` Biprof @cs @ds m = withAppendPSplit @as @cs $ withAppendPSplit @bs @ds $
    Biprof $ psplit (\as cs -> pappend (n as) (m cs))
  r \\\ Biprof{} = r