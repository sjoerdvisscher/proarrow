module Proarrow.Category.Instance.Unit where

import Proarrow.Core (CAT, Category(..), Profunctor(..), type (~>), dimapDefault)

type Unit :: CAT ()
data Unit a b where
  Unit :: Unit '() '()

type instance (~>) = Unit

instance Category Unit where
  type Ob a = a ~ '()
  id = Unit
  Unit . Unit = Unit

instance Profunctor Unit where
  dimap = dimapDefault
  r \\ Unit = r
