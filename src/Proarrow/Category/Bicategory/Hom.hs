module Proarrow.Category.Bicategory.Hom where

import Proarrow.Category.Bicategory (Bicategory (..), (==), (||))
import Proarrow.Category.Bicategory.Co (COK (..), Co (..))
import Proarrow.Category.Bicategory.Prof (LaxProfunctor (..))
import Proarrow.Category.Instance.Nat (Nat (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault, obj, type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Identity (Id (..))

newtype HK kk i j = HomK {unHomK :: kk i j}
type instance UN HomK (HomK k) = k

type HomW :: CAT (HK kk i j)
data HomW a b where
  HomW :: a ~> b -> HomW (HomK a) (HomK b)
instance (Profunctor ((~>) :: CAT (kk i j))) => Profunctor (HomW :: CAT (HK kk i j)) where
  dimap = dimapDefault
  r \\ HomW f = r \\ f
instance (Promonad ((~>) :: CAT (kk i j))) => Promonad (HomW :: CAT (HK kk i j)) where
  id = HomW id
  HomW f . HomW g = HomW (f . g)
instance (CategoryOf (kk i j)) => CategoryOf (HK kk i j) where
  type (~>) = HomW
  type Ob k = (Is HomK k, Ob (UN HomK k))

instance
  (Bicategory kk, Ob s, Ob t, Ob0 kk h, Ob0 kk i, Ob0 kk j, Ob0 kk k)
  => Profunctor (P kk kk (HK kk) (s :: COK kk h i) (t :: kk j k))
  where
  dimap (HomW f) (HomW g) (Hom n) = Hom ((obj @t `o` g) . n . (f `o` obj @(UN CO s))) \\\ f \\\ g
  r \\ Hom{} = r
instance
  (Bicategory kk, Ob s, Ob0 kk h, Ob0 kk i, Ob0 kk j, Ob0 kk k)
  => Functor (P kk kk (HK kk) (s :: COK kk h i) :: kk j k -> HK kk h j +-> HK kk i k)
  where
  map f = (Prof \(Hom @_ @b n) -> Hom ((f `o` obj @b) . n)) \\\ f
instance
  (Bicategory kk, Ob0 kk h, Ob0 kk i, Ob0 kk j, Ob0 kk k)
  => Functor (P kk kk (HK kk) :: COK kk h i -> kk j k -> HK kk h j +-> HK kk i k)
  where
  map (Co f) = (Nat (Prof \(Hom @a n) -> Hom (n . (obj @a `o` f)))) \\\ f

instance (Bicategory kk) => LaxProfunctor kk kk (HK kk) where
  data P kk kk (HK kk) s t a b where
    Hom
      :: forall {h} {i} {j} {k} {kk} (a :: kk i k) (b :: kk h j) (s :: kk h i) (t :: kk j k)
       . (Ob a, Ob b, Ob s, Ob t, Ob0 kk h, Ob0 kk i, Ob0 kk j, Ob0 kk k)
      => a `O` s ~> t `O` b
      -> P kk kk (HK kk) (CO s) t (HomK a) (HomK b)
  laxId (Id (HomW f) :: Id (a :: HK kk i j) b) = Hom (leftUnitorInv . f . rightUnitor) \\ f \\ iObj @kk @i \\ iObj @kk @j
  laxComp (Hom @a @b @s @t n :.: Hom @_ @c @s' @t' m) =
    let s = obj @s; t = obj @t; s' = obj @s'; t' = obj @t'
    in Hom (associatorInv @_ @a @s @s' == n || s' == associator @_ @t @b @s' == t || m == associatorInv @_ @t @t' @c)
        \\\ (s || s')
        \\\ (t || t')
