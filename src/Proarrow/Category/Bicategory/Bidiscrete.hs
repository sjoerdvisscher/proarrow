module Proarrow.Category.Bicategory.Bidiscrete where

import Data.Type.Equality (type (~~))

import Proarrow.Category.Bicategory (BICAT, Bicategory(..), Path(..), IsPath(..), MKKIND)
import Proarrow.Core (Profunctor (..), Promonad (..), CategoryOf(..), dimapDefault)

type VoidK :: MKKIND
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
instance CategoryOf (Path VoidK j k) where
  type (~>) = Bidiscrete
  type Ob @(Path VoidK j k) as = (IsPath as, as ~~ (Nil :: Path VoidK j j))

-- | The bicategory with only identity 1-cells.
instance Bicategory VoidK where
  type Ob0 VoidK k = ()
  type Ob1 VoidK p = ()
  Bidiscrete `o` Bidiscrete = Bidiscrete
  r \\\ Bidiscrete = r