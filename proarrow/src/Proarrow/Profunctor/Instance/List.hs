{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The category @'LIST' k@ of lists of objects of @k@, whose arrows are componentwise lists of arrows.
-- @'List' p@ lifts a profunctor @p@ componentwise to lists. Lists of objects are the arity-indexing used by
-- promonoidal categories ("Proarrow.Category.Promonoidal") and by cones and cocones.
module Proarrow.Profunctor.Instance.List where

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), Strictly (..))

-- import Proarrow.Category.Monoidal.Action (MonoidalAction (..), Strong (..))
import Proarrow.Category.Monoidal.Strictified qualified as Str
import Proarrow.Core (CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, type (+->))
import Proarrow.Functor (Functor (..))

-- import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (Representable (..))

type data LIST k = L [k]

-- | Lifts @p@ componentwise to lists: an arrow between equal-length lists of objects is a list of
-- @p@-arrows.
type List :: (j +-> k) -> LIST j +-> LIST k
data List p as bs where
  Nil :: List p (L '[]) (L '[])
  Cons :: (Str.IsList as, Str.IsList bs) => p a b -> List p (L as) (L bs) -> List p (L (a ': as)) (L (b ': bs))

mkCons :: (Profunctor p) => p a b -> List p (L as) (L bs) -> List p (L (a ': as)) (L (b ': bs))
mkCons f fs = Cons f fs \\ fs

foldList :: (MonoidalProfunctor p) => List p as bs -> p (Str.Fold (UN L as)) (Str.Fold (UN L bs))
foldList Nil = one
foldList (Cons p Nil) = p
foldList (Cons p ps@Cons{}) = p ** foldList ps

instance Functor List where
  map (Prof n) = Prof \case
    Nil -> Nil
    Cons p ps -> Cons (n p) (unProf (map (Prof n)) ps)

-- | The category of lists of arrows.
instance (CategoryOf k) => CategoryOf (LIST k) where
  type (~>) = List (~>)
  type Ob as = (Is L as, Str.IsList (UN L as))

instance (Promonad p) => Promonad (List p) where
  id @(L bs) = case Str.sList @bs of
    Str.SNil -> Nil
    Str.SSing -> Cons id Nil
    Str.SCons -> Cons id id
  Nil . Nil = Nil
  Cons f fs . Cons g gs = Cons (f . g) (fs . gs)

instance (Profunctor p) => Profunctor (List p) where
  dimap Nil Nil Nil = Nil
  dimap (Cons l ls) (Cons r rs) (Cons f fs) =
    Cons (dimap l r f) (dimap ls rs fs)
  dimap Nil Cons{} fs = case fs of {}
  dimap Cons{} Nil fs = case fs of {}
  r \\ Nil = r
  r \\ Cons f Nil = r \\ f
  r \\ Cons f fs@Cons{} = r \\ f \\ fs

-- | The free monoidal profunctor on a profunctor.
instance (Profunctor p) => MonoidalProfunctor (List p) where
  one = Nil
  Nil ** Nil = Nil
  Nil ** gs@Cons{} = gs
  Cons f fs ** Nil = mkCons f (fs ** Nil)
  Cons f fs ** Cons g gs = mkCons f (fs ** Cons g gs)

-- | The free monoidal category on a category.
instance (CategoryOf k) => Monoidal (LIST k) where
  type Unit = L '[]
  type p ** q = L (UN L p Str.++ UN L q)
  withOb2 @(L as) @(L bs) r = Str.withIsList2 @as @bs r
  associator @as @bs @cs = associatorDefault @as @bs @cs
  associatorInv @as @bs @cs = associatorDefault @as @bs @cs

instance (Representable p) => Representable (List p) where
  type List p % L '[] = L '[]
  type List p % L (a ': as) = L ((p % a) ': UN L (List p % L as))
  index Nil = Nil
  index (Cons p Nil) = Cons (index @p p) Nil
  index (Cons p ps@Cons{}) = mkCons (index @p p) (index @(List p) ps)
  tabulate @(L b) Nil = case Str.sList @b of Str.SNil -> Nil
  tabulate @(L b) (Cons f Nil) = case Str.sList @b of Str.SSing -> Cons (tabulate @p f) Nil
  tabulate @(L b) (Cons f fs@Cons{}) = case Str.sList @b of Str.SCons -> Cons (tabulate @p f) (tabulate @(List p) fs)
  repMap Nil = Nil
  repMap (Cons f Nil) = Cons (repMap @p f) Nil
  repMap (Cons f fs@Cons{}) = mkCons (repMap @p f) (repMap @(List p) fs)

instance (DaggerProfunctor p) => DaggerProfunctor (List p) where
  dagger Nil = Nil
  dagger (Cons f fs) = Cons (dagger f) (dagger fs)
