module Proarrow.Category.Instance.Collage where

import Data.Kind (Constraint)

import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Kind
  , Obj
  , Profunctor (..)
  , Promonad (..)
  , dimapDefault
  , lmap
  , obj
  , rmap
  , type (+->)
  )
import Proarrow.Object.Initial (HasInitialObject (..), initiate')
import Proarrow.Object.Terminal (HasTerminalObject (..), terminate')
import Proarrow.Category.Enriched.ThinCategory (CodiscreteProfunctor, Thin, ThinProfunctor (..), anyArr)
import Proarrow.Functor (FunctorForRep (..))

type COLLAGE :: forall {j} {k}. k +-> j -> Kind
type data COLLAGE (p :: k +-> j) = L j | R k

type Collage :: CAT (COLLAGE p)
data Collage a b where
  InL :: a ~> b -> Collage (L a :: COLLAGE p) (L b :: COLLAGE p)
  InR :: a ~> b -> Collage (R a :: COLLAGE p) (R b :: COLLAGE p)
  L2R :: p a b -> Collage (L a :: COLLAGE p) (R b :: COLLAGE p)

type IsLR :: forall {p}. COLLAGE p -> Constraint
class IsLR (a :: COLLAGE p) where
  lrId :: Obj a
instance (Ob a, Promonad ((~>) :: CAT k)) => IsLR (L a :: (COLLAGE (p :: j +-> k))) where
  lrId = InL id
instance (Ob a, Promonad ((~>) :: CAT j)) => IsLR (R a :: (COLLAGE (p :: j +-> k))) where
  lrId = InR id

instance (Profunctor p) => Profunctor (Collage :: CAT (COLLAGE p)) where
  dimap = dimapDefault
  r \\ InL f = r \\ f
  r \\ InR f = r \\ f
  r \\ L2R p = r \\ p

instance (Profunctor p) => Promonad (Collage :: CAT (COLLAGE p)) where
  id = lrId
  InL g . InL f = InL (g . f)
  InR g . L2R p = L2R (rmap g p)
  L2R p . InL f = L2R (lmap f p)
  InR g . InR f = InR (g . f)

-- | The collage of a profunctor.
instance (Profunctor p) => CategoryOf (COLLAGE p) where
  type (~>) = Collage
  type Ob a = IsLR a

instance (HasInitialObject j, CategoryOf k, CodiscreteProfunctor p) => HasInitialObject (COLLAGE (p :: k +-> j)) where
  type InitialObject = L InitialObject
  initiate @a = case obj @a of
    InL a -> InL (initiate' a)
    InR b -> L2R anyArr \\ b

instance (HasTerminalObject k, CategoryOf j, CodiscreteProfunctor p) => HasTerminalObject (COLLAGE (p :: k +-> j)) where
  type TerminalObject = R TerminalObject
  terminate @a = case obj @a of
    InL a -> L2R anyArr \\ a
    InR b -> InR (terminate' b)

class HasArrowCollage p (a :: COLLAGE p) b where arrCoprod :: a ~> b
instance (Thin j, HasArrow (~>) (a :: j) b, Ob a, Ob b) => HasArrowCollage (p :: k +-> j) (L a) (L b) where
  arrCoprod = InL arr
instance (ThinProfunctor p, HasArrow p a b, Ob a, Ob b) => HasArrowCollage (p :: k +-> j) (L a) (R b) where
  arrCoprod = L2R arr
instance (Thin k, HasArrow (~>) (a :: k) b, Ob a, Ob b) => HasArrowCollage (p :: k +-> j) (R a) (R b) where
  arrCoprod = InR arr

instance (Thin j, Thin k, ThinProfunctor p) => ThinProfunctor (Collage :: CAT (COLLAGE (p :: k +-> j))) where
  type HasArrow (Collage :: CAT (COLLAGE p)) a b = HasArrowCollage p a b
  arr = arrCoprod
  withArr (InL f) r = withArr f r \\ f
  withArr (L2R p) r = withArr p r \\ p
  withArr (InR f) r = withArr f r \\ f

data family InjL :: forall (p :: k +-> j) -> j +-> COLLAGE p
instance (Profunctor p) => FunctorForRep (InjL p) where
  type InjL p @ a = L a
  fmap = InL

data family InjR :: forall (p :: k +-> j) -> k +-> COLLAGE p
instance (Profunctor p) => FunctorForRep (InjR p) where
  type InjR p @ a = R a
  fmap = InR