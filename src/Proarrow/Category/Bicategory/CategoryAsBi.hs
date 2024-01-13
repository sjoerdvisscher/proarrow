module Proarrow.Category.Bicategory.CategoryAsBi where

import Prelude (error, ($))

import Proarrow.Core (CAT, CategoryOf(..), Profunctor(..), Promonad(..), dimapDefault)
import Proarrow.Category.Bicategory (BICAT, Path(..), Bicategory(..), SPath(..), IsPath(..), appendObj)
import Proarrow.Object (obj)

type PLAINK :: forall k -> CAT k
data PLAINK k i j = PLAIN -- should be @PLAIN (i ~> j)@ storing a value at type level, but that needs dependent types

type Category :: BICAT (PLAINK k)
data Category as bs where
  Id :: forall {k} a b as. (IsPath as, Ob a, Ob b) => a ~> b -> Category (as :: Path (PLAINK k) (a :: k) (b :: k)) as

instance CategoryOf k => Profunctor (Category :: CAT (Path (PLAINK k) a b)) where
  dimap = dimapDefault
  r \\ Id f = r \\ f
instance CategoryOf k => Promonad (Category :: CAT (Path (PLAINK k) a b)) where
  id :: forall (as :: Path (PLAINK k) a b). Ob as => Category as as
  id = Id $ case singPath @as of
    SNil -> obj @a
    SCons _ -> error "Unimplementable" -- needs dependent types
  Id f . Id _g = Id f -- f and g should be the same, but this isn't checked by the type system
instance CategoryOf k => CategoryOf (Path (PLAINK k) a b) where
  type (~>) = Category
  type Ob (as :: Path (PLAINK k) a b) = (IsPath as, Ob a, Ob b)

-- | A plain category as a (locally discrete) bicategory.
instance CategoryOf k => Bicategory (PLAINK k) where
  type Ob0 (PLAINK k) a = Ob a
  type Ob1 (PLAINK k) p = (p ~ PLAIN)
  Id @_ @_ @ps f `o` Id @_ @_ @qs g = appendObj @ps @qs $ Id (g . f)
  r \\\ Id f = r \\ f