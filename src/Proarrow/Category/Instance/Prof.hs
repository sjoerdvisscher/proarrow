module Proarrow.Category.Instance.Prof where

import Proarrow.Core (CAT, PRO, Category(..), Profunctor(..), type (~>), CategoryOf, dimapDefault, (:~>))
import Proarrow.Object.Terminal (HasTerminalObject(..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts(..))

type Prof :: CAT (PRO j k)
data Prof p q where
  Prof :: (Profunctor p, Profunctor q)
      => { getProf :: p :~> q }
      -> Prof p q

type instance (~>) = Prof

-- | The category of profunctors and natural transformations between them.
instance Category Prof where
  type Ob p = Profunctor p
  id = Prof id
  Prof f . Prof g = Prof (f . g)

instance Profunctor Prof where
  dimap = dimapDefault
  r \\ Prof{} = r

type TerminalProfunctor :: PRO j k
data TerminalProfunctor a b where
  TerminalProfunctor :: (Ob a, Ob b) => TerminalProfunctor a b
instance (CategoryOf j, CategoryOf k) => Profunctor (TerminalProfunctor :: PRO j k) where
  dimap l r TerminalProfunctor = TerminalProfunctor \\ l \\ r
  r \\ TerminalProfunctor = r
instance (CategoryOf j, CategoryOf k) => HasTerminalObject (PRO j k) where
  type TerminalObject = TerminalProfunctor
  terminate' Prof{} = Prof \a -> TerminalProfunctor \\ a

type (:*:) :: PRO j k -> PRO j k -> PRO j k
data (p :*: q) a b where
  (:*:) :: p a b -> q a b -> (p :*: q) a b
instance (Profunctor p, Profunctor q) => Profunctor (p :*: q) where
  dimap l r (p :*: q) = dimap l r p :*: dimap l r q
  r \\ (p :*: _) = r \\ p
instance (CategoryOf j, CategoryOf k) => HasBinaryProducts (PRO j k) where
  type p && q = p :*: q
  fst' Prof{} Prof{} = Prof \(p :*: _) -> p
  snd' Prof{} Prof{} = Prof \(_ :*: q) -> q
  Prof l &&& Prof r = Prof \p -> l p :*: r p