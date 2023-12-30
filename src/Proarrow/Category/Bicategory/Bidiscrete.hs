module Proarrow.Category.Bicategory.Bidiscrete where

import Proarrow.Category.Bicategory (BICAT, Bicategory(..), Path(..))
import Proarrow.Core (Profunctor (..), Promonad (..), CategoryOf(..), dimapDefault)

data VoidK j k
type Bidiscrete :: BICAT VoidK
data Bidiscrete as bs where
  Bidiscrete :: Bidiscrete Nil Nil

instance Profunctor Bidiscrete where
  dimap = dimapDefault
  r \\ Bidiscrete = r

instance Promonad Bidiscrete where
  id = bidiscId
  Bidiscrete . Bidiscrete = Bidiscrete

class IsVoidPath (as :: Path VoidK j k) where
  bidiscId :: Bidiscrete as as
instance IsVoidPath Nil where
  bidiscId = Bidiscrete

instance CategoryOf (Path VoidK j k) where
  type (~>) = Bidiscrete
  type Ob @(Path VoidK j k) as = (IsVoidPath as, j ~ k)

-- | The bicategory with only identity arrows.
instance Bicategory VoidK where
  type Ob0 VoidK k = ()
  type Ob1 VoidK p = ()
  Bidiscrete `o` Bidiscrete = Bidiscrete
  r \\\ Bidiscrete = r