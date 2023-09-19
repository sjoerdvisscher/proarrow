{-# LANGUAGE UndecidableInstances #-}
module Proarrow.Promonad where

import Proarrow.Core (CAT, PRO, Category(..), Profunctor(..), (:~>), type (~>), dimapDefault, rmap, (//), CategoryOf)
import Proarrow.Profunctor.Composition ((:.:)(..), Comp)
import Proarrow.Adjunction (Adjunction)
import Proarrow.Adjunction qualified as Adj
import Proarrow.Monoid qualified as Mon
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Profunctor.Identity (Id(..))

class Profunctor p => Promonad p where
  unit :: (~>) :~> p
  mult :: p :.: p :~> p

newtype TAG (p :: CAT k) = TAG { unTAG :: k }
-- can't use unTAG at the type level
type family UNTAG (a :: TAG (p :: CAT k)) :: k where UNTAG ('TAG k) = k

type Tag :: CAT (TAG p)
data Tag (a :: TAG p) b where
  Tag :: p a b -> Tag ('TAG a :: TAG p) ('TAG b)

type instance (~>) = Tag

instance Promonad p => Profunctor (Tag :: CAT (TAG p)) where
  dimap = dimapDefault
  r \\ Tag p = r \\ p

-- | Every promonad makes a category.
instance Promonad p => Category (Tag :: CAT (TAG p)) where
  type Ob a = (a ~ 'TAG (UNTAG a), Ob (UNTAG a))
  id = Tag (unit @p id)
  Tag f . Tag g = Tag (mult @p (f :.: g))

instance Adjunction p q => Promonad (p :.: q) where
  unit f = f // rmap f Adj.unit
  mult ((p :.: q) :.: (p' :.: q')) = p :.: rmap (Adj.counit (q :.: p')) q'

instance CategoryOf k => Mon.Monoid (Promonad p) (p :: PRO k k) where
  type Ten (Promonad p) = Comp
  unit = Prof \(Id f) -> unit f
  mult = Prof mult