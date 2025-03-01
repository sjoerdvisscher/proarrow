module Proarrow.Category.Bicategory.CategoryAsBi where

import Prelude (Maybe (..), liftA2, (>>), type (~))

import Proarrow.Category.Bicategory (Bicategory (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault)

type PLAINK :: forall k -> CAT k
data PLAINK k i j = PLAIN -- should be @PLAIN (i ~> j)@ storing a value at type level, but that needs dependent types

type Category :: CAT (PLAINK k i j)
data Category as bs where
  Id :: forall {k} a b. (Ob a, Ob b) => Maybe (a ~> b) -> Category (PLAIN :: PLAINK k (a :: k) (b :: k)) PLAIN

instance (CategoryOf k, Ob i, Ob j) => Profunctor (Category :: CAT (PLAINK k i j)) where
  dimap = dimapDefault
  r \\ Id{} = r
instance (CategoryOf k, Ob i, Ob j) => Promonad (Category :: CAT (PLAINK k i j)) where
  id = Id Nothing
  Id f . Id g = Id (f >> g) -- f and g should be the same, but this isn't checked by the type system
instance (CategoryOf k, Ob i, Ob j) => CategoryOf (PLAINK k i j) where
  type (~>) = Category
  type Ob a = (a ~ PLAIN)

instance (CategoryOf k) => Bicategory (PLAINK k) where
  type Ob0 (PLAINK k) a = Ob a
  type I = PLAIN
  type O PLAIN PLAIN = PLAIN
  withOb2 r = r
  r \\\ Id{} = r
  Id f `o` Id g = Id (liftA2 (.) f g)
  leftUnitor = id
  leftUnitorInv = id
  rightUnitor = id
  rightUnitorInv = id
  associator = id
  associatorInv = id
