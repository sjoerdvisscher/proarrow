{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Bicategory.Terminal where

import Proarrow.Category.Bicategory (Bicategory(..), BICAT, Path(..), IsPath (..), SPath (..))
import Proarrow.Core (CategoryOf(..), Profunctor(..), CAT, Promonad (..), dimapDefault)

data TK = T
type TERMK :: CAT TK
data TERMK j k

type Terminal :: BICAT TERMK
data Terminal as bs where
  Terminal :: Terminal (Nil :: Path TERMK T T) (Nil :: Path TERMK T T)

instance (j ~ T, k ~ T) => Profunctor (Terminal :: CAT (Path TERMK j k)) where
  dimap = dimapDefault
  r \\ Terminal = r
instance (j ~ T, k ~ T) => Promonad (Terminal :: CAT (Path TERMK j k)) where
  id :: forall ps. Ob ps => Terminal ps ps
  id = case singPath @ps of
    SNil -> Terminal
    (SCons @p _) -> isBottom @p
  Terminal . Terminal = Terminal
instance (j ~ T, k ~ T) => CategoryOf (Path TERMK j k) where
  type (~>) = Terminal
  type Ob (ps :: Path TERMK j k) = IsPath ps

class IsBottom (p :: TERMK T T) where isBottom :: a

-- | The terminal bicategory, with a single 0-cell @T@, a single identity 1-cell @Nil :: Path TERMK T T@, and a single identity 2-cell @Terminal@.
instance Bicategory TERMK where
  type Ob0 TERMK k = (k ~ T)
  type Ob1 TERMK p = IsBottom p
  Terminal `o` Terminal = Terminal
  r \\\ Terminal = r