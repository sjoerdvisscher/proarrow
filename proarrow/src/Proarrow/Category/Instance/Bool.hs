-- | The thin category of booleans: objects 'FLS' and 'TRU' with one non-identity arrow
-- @'FLS' '~>' 'TRU'@ -- the poset @False <= True@, a.k.a. the walking arrow. It is a core type:
-- thin categories are enriched in it ("Proarrow.Category.Enriched.Thin"), so this module depends
-- on nothing but "Proarrow.Core", and @BOOL@'s further structure -- conjunction as product and
-- tensor, disjunction as coproduct, closed, star-autonomous, (co)equalizers, pullbacks\/pushouts,
-- a parameterized NNO -- is instantiated in the modules that define those classes.
module Proarrow.Category.Instance.Bool where

import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, type (+->))
import Prelude qualified as P

data BOOL = FLS | TRU

type Booleans :: CAT BOOL
data Booleans a b where
  Fls :: Booleans FLS FLS
  F2T :: Booleans FLS TRU
  Tru :: Booleans TRU TRU

deriving instance P.Eq (Booleans a b)
deriving instance P.Show (Booleans a b)

-- | Negation; the 'Proarrow.Category.Monoidal.StarAutonomous.Dual' of @BOOL@.
type family Not (b :: BOOL) :: BOOL where
  Not FLS = TRU
  Not TRU = FLS

class (IsBool (Not b)) => IsBool (b :: BOOL) where boolId :: b ~> b
instance IsBool FLS where boolId = Fls
instance IsBool TRU where boolId = Tru

-- | The category of 2 objects and one arrow between them, a.k.a. the walking arrow.
instance CategoryOf BOOL where
  type (~>) = Booleans
  type Ob b = IsBool b

instance Promonad Booleans where
  id = boolId
  Fls . Fls = Fls
  F2T . Fls = F2T
  Tru . F2T = F2T
  Tru . Tru = Tru

instance Profunctor Booleans where
  dimap = dimapDefault
  r \\ Fls = r
  r \\ F2T = r
  r \\ Tru = r

-- | @a <= b@ on the walking arrow, as a 'BOOL' again: the hom of the walking arrow is its own
-- internal hom.
type family BoolLeq (a :: BOOL) (b :: BOOL) :: BOOL where
  BoolLeq TRU FLS = FLS
  BoolLeq a b = TRU

-- | The four non-trivial profunctors @BOOL '+->' BOOL@, indexed by a pair of 'BOOL's selecting
-- whether the @FLS->FLS@ and @TRU->TRU@ heteromorphisms are present; @FLS->TRU@ always is.
type NonTrivialProfunctor :: (BOOL, BOOL) -> BOOL +-> BOOL
data NonTrivialProfunctor ft a b where
  FF :: NonTrivialProfunctor '(TRU, tt) FLS FLS
  FT :: NonTrivialProfunctor ft FLS TRU
  TT :: NonTrivialProfunctor '(ff, TRU) TRU TRU

deriving instance P.Eq (NonTrivialProfunctor ft a b)
deriving instance P.Show (NonTrivialProfunctor ft a b)

instance Profunctor (NonTrivialProfunctor ft) where
  dimap Fls Fls FF = FF
  dimap Fls F2T FF = FT
  dimap Fls Tru FT = FT
  dimap F2T Tru TT = FT
  dimap Tru Tru TT = TT
  dimap F2T Fls x = case x of {}
  dimap Tru Fls x = case x of {}
  dimap Tru F2T x = case x of {}
  dimap F2T F2T x = case x of {}
  r \\ FF = r
  r \\ FT = r
  r \\ TT = r

-- | Which heteromorphisms @'NonTrivialProfunctor' '(ff, tt)@ has.
type family NonTrivialHolds (ff :: BOOL) (tt :: BOOL) (a :: BOOL) (b :: BOOL) :: BOOL where
  NonTrivialHolds ff tt FLS FLS = ff
  NonTrivialHolds ff tt FLS TRU = TRU
  NonTrivialHolds ff tt TRU TRU = tt
  NonTrivialHolds ff tt TRU FLS = FLS
