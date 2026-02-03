{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Profunctor.List where

import Data.Kind (Type)

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), Strong (..), actHom)
import Proarrow.Category.Monoidal.Strictified qualified as Str
import Proarrow.Core (CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Representable (Representable (..))

type data LIST k = L [k]
type instance UN L (L as) = as

type List :: (j +-> k) -> LIST j +-> LIST k
data List p as bs where
  Nil :: List p (L '[]) (L '[])
  Cons :: (Str.IsList as, Str.IsList bs) => p a b -> List p (L as) (L bs) -> List p (L (a ': as)) (L (b ': bs))

mkCons :: (Profunctor p) => p a b -> List p (L as) (L bs) -> List p (L (a ': as)) (L (b ': bs))
mkCons f fs = Cons f fs \\ fs

foldList :: (MonoidalProfunctor p) => List p as bs -> p (Str.Fold (UN L as)) (Str.Fold (UN L bs))
foldList Nil = par0
foldList (Cons p Nil) = p
foldList (Cons p ps@Cons{}) = p `par` foldList ps

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
  par0 = Nil
  Nil `par` Nil = Nil
  Nil `par` gs@Cons{} = gs
  Cons f fs `par` Nil = mkCons f (fs `par` Nil)
  Cons f fs `par` Cons g gs = mkCons f (fs `par` Cons g gs)

-- | The free monoidal category on a category.
instance (CategoryOf k) => Monoidal (LIST k) where
  type Unit = L '[]
  type p ** q = L (UN L p Str.++ UN L q)
  withOb2 @(L as) @(L bs) r = Str.withIsList2 @as @bs r
  leftUnitor = id
  leftUnitorInv = id
  rightUnitor = id
  rightUnitorInv = id
  associator @as @bs @cs = withOb2 @_ @as @bs (withOb2 @_ @(as ** bs) @cs (id @(List (~>))))
  associatorInv @as @bs @cs = withOb2 @_ @bs @cs (withOb2 @_ @as @(bs ** cs) (id @(List (~>))))

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

instance (MonoidalAction Type k, Strong Type (Id :: k +-> k)) => MonoidalAction Type (LIST k) where
  type Act (a :: Type) (L '[] :: LIST k) = L '[]
  type Act (a :: Type) (L (b ': bs) :: LIST k) = L (Act a b ': UN L (Act a (L bs)))
  withObAct @a @(L xs) r = case Str.sList @xs of
    Str.SNil -> r
    Str.SSing @x -> withObAct @Type @k @a @x r
    Str.SCons @x @(y ': ys) -> withObAct @Type @(LIST k) @a @(L ys) (withObAct @Type @(LIST k) @a @(L (y ': ys)) (withObAct @Type @k @a @x r))
  unitor @(L xs) = case Str.sList @xs of
    Str.SNil -> Nil
    Str.SSing @x -> Cons (unitor @Type @k @x) Nil
    Str.SCons @x @xs' -> mkCons (unitor @Type @k @x) (unitor @Type @(LIST k) @(L xs'))
  unitorInv @(L xs) = case Str.sList @xs of
    Str.SNil -> Nil
    Str.SSing @x -> Cons (unitorInv @Type @k @x) Nil
    Str.SCons @x @xs' -> mkCons (unitorInv @Type @k @x) (unitorInv @Type @(LIST k) @(L xs'))
  multiplicator @a @b @(L xs) = case Str.sList @xs of
    Str.SNil -> Nil
    Str.SSing @x -> Cons (multiplicator @Type @k @a @b @x) Nil
    Str.SCons @x @xs' -> mkCons (multiplicator @Type @k @a @b @x) (multiplicator @Type @(LIST k) @a @b @(L xs'))
  multiplicatorInv @a @b @(L xs) = case Str.sList @xs of
    Str.SNil -> Nil
    Str.SSing @x -> Cons (multiplicatorInv @Type @k @a @b @x) Nil
    Str.SCons @x @xs' -> mkCons (multiplicatorInv @Type @k @a @b @x) (multiplicatorInv @Type @(LIST k) @a @b @(L xs'))

instance (Strong Type p) => Strong Type (List p) where
  act _ Nil = Nil
  act f (Cons g Nil) = Cons (act f g) Nil
  act f (Cons g gs@Cons{}) = mkCons (act f g) (act f gs)

instance (Strong Type (Id :: k +-> k)) => Strong Type (Id :: LIST k +-> LIST k) where
  act _ (Id Nil) = Id Nil
  act f (Id (Cons g Nil)) = Id (Cons (actHom f g) Nil)
  act f (Id (Cons g gs@Cons{})) = Id (mkCons (actHom f g) (actHom f gs))
