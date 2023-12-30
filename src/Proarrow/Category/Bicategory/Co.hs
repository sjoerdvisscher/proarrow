module Proarrow.Category.Bicategory.Co where

import Data.Function (($))
import Data.Kind (Type)
import Fcf.Core (Eval)

import Proarrow.Category.Bicategory (Bicategory(..), MKKIND, BICAT, Path(..), IsPath, withAppendIsPath, MapPath, Eval', MapFunc)
import Proarrow.Core (CategoryOf(..), Profunctor(..), CAT, Promonad (..), dimapDefault, UN, Is)


type COK :: MKKIND -> MKKIND
newtype COK kk j k = CO (kk j k)
type instance UN CO (CO k) = k


data UnCO :: MapFunc (COK kk) kk -> Type
type instance Eval' UnCO (CO p) = p

type UnCoPath :: Path (COK kk) a b -> Path kk a b
type UnCoPath ps = Eval (MapPath UnCO ps)

type Co :: BICAT (COK kk)
data Co as bs where
  Co :: (Ob as, Ob bs) => UnCoPath bs ~> UnCoPath as -> Co as bs

instance (CategoryOf (Path kk j k)) => Profunctor (Co :: CAT (Path (COK kk) j k)) where
  dimap = dimapDefault
  r \\ Co f = r \\ f
instance (CategoryOf (Path kk j k)) => Promonad (Co :: CAT (Path (COK kk) j k)) where
  id = Co id
  Co f . Co g = Co (g . f)
instance (CategoryOf (Path kk j k)) => CategoryOf (Path (COK kk) j k) where
  type (~>) = Co
  type Ob (fs :: Path (COK kk) j k) = IsPath fs UnCO

instance Bicategory kk => Bicategory (COK kk) where
  type Ob0 (COK kk) k = Ob0 kk k
  type Ob1 (COK kk) p = (Is CO p, Ob1 kk (UN CO p))
  Co @as @bs f `o` Co @cs @ds g = withAppendIsPath @as @cs @UnCO $ withAppendIsPath @bs @ds @UnCO $ Co (f `o` g)
  r \\\ Co f = r \\\ f