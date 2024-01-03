module Proarrow.Category.Bicategory.Bidiscrete where

import Data.Type.Equality (type (~~))

import Proarrow.Category.Bicategory (BICAT, Bicategory(..), Path(..), IsPath(..))
import Proarrow.Core (Profunctor (..), Promonad (..), CategoryOf(..), dimapDefault)

data VoidK j k
type Bidiscrete :: BICAT VoidK
data Bidiscrete as bs where
  Bidiscrete :: Bidiscrete (Nil :: Path VoidK j j) Nil

instance Profunctor Bidiscrete where
  dimap = dimapDefault
  r \\ Bidiscrete = r

instance Promonad Bidiscrete where
  id = Bidiscrete
  Bidiscrete . Bidiscrete = Bidiscrete

class IsVoidPath (as :: Path VoidK j k) where
  bidiscId :: Bidiscrete as as
instance IsVoidPath Nil where
  bidiscId = Bidiscrete

instance CategoryOf (Path VoidK j k) where
  type (~>) = Bidiscrete
  type Ob @(Path VoidK j k) as = (IsPath as, as ~~ (Nil :: Path VoidK j j))

-- | The bicategory with only identity 1-cells.
instance Bicategory VoidK where
  type Ob0 VoidK k = ()
  type Ob1 VoidK p = ()
  Bidiscrete `o` Bidiscrete = Bidiscrete
  r \\\ Bidiscrete = r