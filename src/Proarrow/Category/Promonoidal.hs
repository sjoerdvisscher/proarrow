{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Promonoidal where

import Data.Kind (Constraint)
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Strictified qualified as Str
import Proarrow.Core
  ( CategoryOf (..)
  , Obj
  , Profunctor (..)
  , Promonad (..)
  , UN
  , lmap
  , obj
  , tgt
  , (//)
  , (:~>)
  , type (+->)
  )
import Proarrow.Functor (Functor (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.List (LIST (..), List (..), foldList)
import Proarrow.Profunctor.Representable (Representable (..), dimapRep)

type PROTENSOR k = LIST k +-> k
type Protensor :: forall {k}. PROTENSOR k -> Constraint
class (Profunctor p) => Protensor p where
  compose :: (p :.: List p) a bss -> p a (Tensor % bss)
  decompose :: (Ob bss) => p a (Tensor % bss) -> (p :.: List p) a bss

class (Protensor p) => Promonoid p m where
  mempty :: p m (L '[])
  mappend :: p m (L '[m, m])

class (Protensor t, Profunctor p) => PromonoidalProfunctor t p where
  parN :: t :.: List p :~> p :.: t

type Tensor :: PROTENSOR k
data Tensor a bs where
  Tensor :: (Ob bs) => {unTensor :: '[a] ~> UN L bs} -> Tensor a bs
instance (Monoidal k) => Profunctor (Tensor :: PROTENSOR k) where
  dimap = dimapRep
  r \\ Tensor (Str.Str f) = r \\ f
instance (Monoidal k) => Representable (Tensor :: PROTENSOR k) where
  type Tensor % as = Str.Fold (UN L as)
  index (Tensor (Str.Str f)) = f
  tabulate f = Tensor (Str.Str f) \\ f
  repMap = foldList
instance (Monoidal k) => MonoidalProfunctor (Tensor :: PROTENSOR k) where
  par0 = Tensor (Str.Str id)
  Tensor f `par` Tensor g = let fg = f `par` g in fg // Str.unStr fg // Tensor (Str.Str (Str.unStr fg))
instance (Monoidal k) => Protensor (Tensor :: PROTENSOR k) where
  compose (Tensor (Str.Str f) :.: l) = lmap f (foldList l)
  decompose @bss (Tensor (Str.Str f)) = lmap f (go (obj @bss))
    where
      -- 🤮
      go :: (Monoidal k) => Obj (ass :: LIST (LIST k)) -> (Tensor :.: List Tensor) (Tensor % (Tensor % ass)) ass
      go Nil = Tensor (Str.Str id) :.: Nil
      go (Cons as Nil) = let fas = foldList as in as // fas // Tensor (Str.Str fas) :.: Cons (Tensor (Str.Str id)) Nil
      go (Cons @ass' @_ @_ @as as ass@Cons{}) = case go ass of
        Tensor @bs g :.: l ->
          as //
            let fas = foldList as; fass = foldList ass
            in fas //
                 fass //
                   let fasg = Str.Str @(UN L as) @'[Str.Fold (UN L as)] fas `par` Str.Str @(UN L (Str.Fold ass')) @(UN L bs) (Str.unStr g)
                   in foldList (as `par` fass) // fasg // (Tensor (Str.Str (Str.unStr fasg))) :.: Cons (Tensor (Str.Str id)) l

instance (MonoidalProfunctor p) => PromonoidalProfunctor Tensor p where
  parN (Tensor (Str.Str f) :.: l) = let fl = foldList l in lmap f fl :.: Tensor (Str.Str (tgt fl)) \\ fl \\ l

type PList :: LIST (j +-> k) -> LIST j +-> LIST k
data PList ps as bs where
  PNil :: PList (L '[]) (L '[]) (L '[])
  PCons
    :: (Ob as, Ob bs, Ob p, Ob ps) => p a b -> PList (L ps) (L as) (L bs) -> PList (L (p ': ps)) (L (a ': as)) (L (b ': bs))
instance (CategoryOf j, CategoryOf k, Ob ps) => Profunctor (PList ps :: LIST j +-> LIST k) where
  dimap Nil Nil PNil = PNil
  dimap (Cons l ls) (Cons r rs) (PCons f fs) =
    ls //
      rs //
        PCons (dimap l r f) (dimap ls rs fs)
  dimap Nil Cons{} ps = case ps of {}
  dimap Cons{} Nil ps = case ps of {}
  r \\ PNil = r
  r \\ PCons f PNil = r \\ f
  r \\ PCons f fs@PCons{} = r \\ f \\ fs
instance (CategoryOf j, CategoryOf k) => Functor (PList :: LIST (j +-> k) -> LIST j +-> LIST k) where
  map Nil = Prof \PNil -> PNil
  map f@(Cons (Prof n) fs) = f // Prof (\(PCons p ps) -> PCons (n p) (unProf (map fs) ps))

type Day :: PROTENSOR k -> PROTENSOR j -> LIST (j +-> k) -> j +-> k
data Day tk tj ps a b where
  Day :: (Ob a, Ob b) => (tj b bs -> (tk a as, PList ps as bs)) -> Day tk tj ps a b
instance (Profunctor tk, Profunctor tj) => Profunctor (Day tk tj ps) where
  dimap l r (Day f) =
    l // r // Day \tj -> case f (lmap r tj) of
      (tk, ps) -> (lmap l tk, ps)
  r \\ Day{} = r
instance (Profunctor tk, Profunctor tj) => Functor (Day tk tj) where
  map f = Prof (\(Day d) -> Day \k -> case d k of (tk, ps) -> (tk, unProf (map f) ps))
