{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Instance.Constraint (CONSTRAINT (..), (:-) (..), (:=>) (..), reifyExp, eqIsSuperOrd, maybeLiftsSemigroup) where

import Data.Kind (Constraint)
import Prelude qualified as P

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault)
import Proarrow.Monoid (Comonoid (..), Monoid (..), CopyDiscard)
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.BinaryProduct qualified as P
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Preorder.ThinCategory (ThinProfunctor (..))
import Unsafe.Coerce (unsafeCoerce)

newtype CONSTRAINT = CNSTRNT Constraint
type instance UN CNSTRNT (CNSTRNT a) = a

data (:-) a b where
  Entails :: {unEntails :: forall r. (a) => ((b) => r) -> r} -> CNSTRNT a :- CNSTRNT b

-- | The category of type class constraints. An arrow from constraint a to constraint b
-- | means that a implies b, i.e. if a holds then b holds.
instance CategoryOf CONSTRAINT where
  type (~>) = (:-)
  type Ob a = (Is CNSTRNT a)

instance Promonad (:-) where
  id = Entails \r -> r
  Entails f . Entails g = Entails \r -> g (f r)

instance Profunctor (:-) where
  dimap = dimapDefault
  r \\ Entails{} = r

instance ThinProfunctor (:-) where
  type HasArrow (:-) a b = UN CNSTRNT a :=> UN CNSTRNT b
  arr @(CNSTRNT a) @(CNSTRNT b) = Entails \r -> unEntails (entails @a @b) r
  withArr p@Entails{} = reifyExp p

instance HasTerminalObject CONSTRAINT where
  type TerminalObject = CNSTRNT ()
  terminate = Entails \r -> r

instance HasBinaryProducts CONSTRAINT where
  type CNSTRNT l && CNSTRNT r = CNSTRNT (l, r)
  withObProd r = r
  fst = Entails \r -> r
  snd = Entails \r -> r
  Entails f &&& Entails g = Entails \r -> f (g r)

instance MonoidalProfunctor (:-) where
  par0 = id
  f `par` g = f *** g

-- | Products as monoidal structure.
instance Monoidal CONSTRAINT where
  type Unit = TerminalObject
  type a ** b = a && b
  withOb2 r = r
  leftUnitor = P.leftUnitorProd
  leftUnitorInv = P.leftUnitorProdInv
  rightUnitor = P.rightUnitorProd
  rightUnitorInv = P.rightUnitorProdInv
  associator = P.associatorProd
  associatorInv = P.associatorProdInv

instance SymMonoidal CONSTRAINT where
  swap = Entails \r -> r

instance Monoid (CNSTRNT ()) where
  mempty = id
  mappend = Entails \r -> r

instance Comonoid (CNSTRNT a) where
  counit = Entails \r -> r
  comult = Entails \r -> r
instance CopyDiscard CONSTRAINT

class b :=> c where
  entails :: CNSTRNT b :- CNSTRNT c
instance (b => c) => (b :=> c) where
  entails = Entails \r -> r

-- magic from reflection library
newtype Magic b c r = Magic ((b :=> c) => r)

reifyExp :: forall b c r. CNSTRNT b :- CNSTRNT c -> ((b :=> c) => r) -> r
reifyExp bc k = unsafeCoerce (Magic k :: Magic b c r) bc
{-# INLINE reifyExp #-}

instance Closed CONSTRAINT where
  type a ~~> b = CNSTRNT (UN CNSTRNT a :=> UN CNSTRNT b)
  withObExp r = r
  curry @_ @(CNSTRNT b) (Entails @_ @c f) = Entails \r -> reifyExp (Entails @b @c f) r
  apply @(CNSTRNT a) @(CNSTRNT b) = Entails \r -> unEntails (entails @a @b) r

eqIsSuperOrd :: CNSTRNT (P.Ord a) :- CNSTRNT (P.Eq a)
eqIsSuperOrd = Entails \r -> r

maybeLiftsSemigroup :: CNSTRNT (P.Semigroup a) :- CNSTRNT (Monoid (P.Maybe a))
maybeLiftsSemigroup = Entails \r -> r
