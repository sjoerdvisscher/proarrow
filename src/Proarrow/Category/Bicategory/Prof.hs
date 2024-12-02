module Proarrow.Category.Bicategory.Prof where

import Data.Kind (Constraint, Type)
import Prelude (($))

import Data.Proxy (Proxy (..))
import Data.Reflection (Reifies (..), reify)
import Proarrow.Adjunction qualified as A
import Proarrow.Category.Bicategory
  ( Adjunction (..)
  , Bicategory (..)
  , Bimodule (..)
  , Comonad (..)
  , Monad (..)
  )
import Proarrow.Category.Bicategory.Co (COK (..), Co (..))
import Proarrow.Category.Bicategory.Kan (RightKanExtension (..), RightKanLift (..))
import Proarrow.Category.Bicategory.Sub (IsOb, SUBCAT (..), Sub (..))
import Proarrow.Category.Colimit qualified as L
import Proarrow.Category.Equipment (Equipment (..), HasCompanions (..), Sq (..), vArr)
import Proarrow.Category.Equipment.Limit (HasColimits (..), HasLimits (..))
import Proarrow.Category.Instance.Collage (COLLAGE (..), Collage (..), InjL (..), InjR (..))
import Proarrow.Category.Instance.Nat (Nat (..))
import Proarrow.Category.Instance.Prof (unProf)
import Proarrow.Category.Limit qualified as L
import Proarrow.Category.Opposite qualified as Op
import Proarrow.Core
  ( CAT
  , Category
  , CategoryOf (..)
  , Is
  , Profunctor (..)
  , Promonad (..)
  , UN
  , arr
  , dimapDefault
  , lmap
  , obj
  , rmap
  , src
  , tgt
  , (//)
  , (:~>)
  , type (+->)
  )
import Proarrow.Functor (Functor (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Ran qualified as R
import Proarrow.Profunctor.Representable (RepCostar (..), Representable (..), dimapRep)
import Proarrow.Profunctor.Rift qualified as R
import Proarrow.Promonad (Procomonad (..))

type data PROFK j k = PK (j +-> k)
type instance UN PK (PK p) = p

type Prof :: CAT (PROFK j k)
data Prof p q where
  Prof :: (Ob p, Ob q) => p :~> q -> Prof (PK p) (PK q)

instance Profunctor Prof where
  dimap = dimapDefault
  r \\ Prof n = r \\ n
instance Promonad Prof where
  id = Prof id
  Prof m . Prof n = Prof (m . n)
instance CategoryOf (PROFK j k) where
  type (~>) = Prof
  type Ob p = (Is PK p, Profunctor (UN PK p))

instance Bicategory PROFK where
  type Ob0 PROFK k = CategoryOf k
  type I = PK Id
  type p `O` q = PK (UN PK p :.: UN PK q)
  Prof m `o` Prof n = Prof $ \(p :.: q) -> m p :.: n q
  r \\\ Prof{} = r
  leftUnitor (Prof n) = Prof $ \(Id h :.: q) -> n (lmap h q)
  leftUnitorInv (Prof n) = Prof $ \p -> Id (src p) :.: n p
  rightUnitor (Prof n) = Prof $ \(p :.: Id h) -> n (rmap h p)
  rightUnitorInv (Prof n) = Prof $ \p -> n p :.: Id (tgt p)
  associator Prof{} Prof{} Prof{} = Prof $ \((p :.: q) :.: r) -> p :.: (q :.: r)
  associatorInv Prof{} Prof{} Prof{} = Prof $ \(p :.: (q :.: r)) -> (p :.: q) :.: r

data ProfRep
type instance IsOb ProfRep p = Representable (UN PK p)

type FUNK = SUBCAT ProfRep PROFK
type FUN p = SUB @ProfRep (PK p)
type UNFUN p = UN PK (UN SUB p)

instance HasCompanions PROFK FUNK where
  type Companion PROFK p = PK (UNFUN p)
  mapCompanion (Sub (Prof n)) = Prof n
  compToId = Prof id
  compFromId = Prof id
  compToCompose f g = Prof id \\ f \\ g
  compFromCompose f g = Prof id \\ f \\ g

instance Equipment PROFK FUNK where
  type Conjoint PROFK p = PK (RepCostar (UNFUN p))
  mapConjoint (Sub (Prof @p n)) = Prof \(RepCostar @a f) -> RepCostar (f . index (n (tabulate @p @a (repMap @p @a id))))
  conjToId = Prof (Id . unRepCostar)
  conjFromId = Prof \(Id f) -> RepCostar f \\ f
  conjToCompose (Sub Prof{}) (Sub (Prof @g _)) = Prof \(RepCostar @b h) -> RepCostar id :.: RepCostar h \\ repMap @g (obj @b)
  conjFromCompose (Sub (Prof @f _)) (Sub Prof{}) = Prof \(RepCostar f :.: RepCostar g) -> RepCostar (g . repMap @f f)

instance (Promonad p) => Monad (PK p :: PROFK k k) where
  eta = Prof (arr . unId)
  mu = Prof \(p :.: q) -> q . p

instance (Procomonad p) => Comonad (PK p :: PROFK k k) where
  epsilon = Prof (Id . extract)
  delta = Prof duplicate

instance
  (Category (cj :: CAT j), Category (ck :: CAT k), Profunctor p)
  => Bimodule (PK ck) (PK cj) (PK p :: PROFK j k)
  where
  leftAction = Prof \(f :.: p) -> lmap f p
  rightAction = Prof \(p :.: f) -> rmap f p

instance (A.Adjunction l r) => Adjunction (PK l :: PROFK c d) (PK r) where
  unit = Prof \(Id f) -> lmap f A.unit \\ f
  counit = Prof (Id . A.counit)

instance (Profunctor f, Profunctor j) => RightKanExtension (PK j :: PROFK c d) (PK f :: PROFK c e) where
  type Ran (PK j) (PK f) = PK (R.Ran (Op.OP j) f)
  ran = Prof \(r :.: j) -> R.runRan j r
  ranUniv (Prof n) = Prof \g -> g // R.Ran \j -> n (g :.: j)

instance (Profunctor f, Profunctor j) => RightKanLift (PK j :: PROFK d c) (PK f :: PROFK e c) where
  type Rift (PK j) (PK f) = PK (R.Rift (Op.OP j) f)
  rift = Prof \(j :.: r) -> R.runRift j r
  riftUniv (Prof n) = Prof \g -> g // R.Rift \j -> n (j :.: g)

instance (L.HasLimits j k, Ob j) => HasLimits FUNK (PK j) k where
  type Limit (PK j) d = FUN (L.Limit j (UNFUN d))
  limitObj = Sub (Prof id)
  limit = Prof L.limit
  limitUniv (Prof n) = Sub (Prof (L.limitUniv n))

instance (L.HasColimits j k, Ob j) => HasColimits FUNK (PK j) k where
  type Colimit (PK j) d = FUN (L.Colimit j (UNFUN d))
  colimit = Prof L.colimit
  colimitUniv (Prof n) = Sub (Prof (L.colimitUniv n))

class
  ( forall (s :: COK sk h i) (t :: tk j k). (Ob s, Ob t) => Profunctor (p s t)
  , forall (s :: COK sk h i). (Ob s) => Functor (p s)
  , Functor p
  ) =>
  IsFunctorial h i j k (p :: COK sk h i -> tk j k -> kk h j +-> kk i k)
instance
  ( forall (s :: COK sk h i) (t :: tk j k). (Ob s, Ob t) => Profunctor (p s t)
  , forall (s :: COK sk h i). (Ob s) => Functor (p s)
  , Functor p
  )
  => IsFunctorial h i j k (p :: COK sk h i -> tk j k -> kk h j +-> kk i k)

type LaxProfunctor :: forall {s} {t}. CAT s -> CAT t -> (t +-> s) -> Constraint
class
  ( Bicategory sk
  , Bicategory tk
  , forall h i j k. (Ob0 sk h, Ob0 sk i, Ob0 tk j, Ob0 tk k) => IsFunctorial h i j k (P sk tk kk)
  , forall j k. (Ob0 sk j, Ob0 tk k) => CategoryOf (kk j k)
  ) =>
  LaxProfunctor (sk :: CAT s) (tk :: CAT t) (kk :: t +-> s)
  where
  data P sk tk kk :: forall {h} {i} {j} {k}. COK sk h i -> tk j k -> kk h j +-> kk i k
  laxId :: (Ob0 sk k, Ob0 tk j) => (Id :: CAT (kk k j)) :~> P sk tk kk (CO (I :: sk k k)) (I :: tk j j)
  laxComp :: P sk tk kk s0 t0 :.: P sk tk kk s1 t1 :~> P sk tk kk (s0 `O` s1) (t0 `O` t1)

dimapLax :: (LaxProfunctor sk tk kk) => (s' ~> s) -> (t ~> t') -> P sk tk kk (CO s) t :~> P sk tk kk (CO s') t'
dimapLax f g = (unProf (unNat (map (Co f))) . unProf (map g)) \\\ f \\\ g

instance (Monad m, Comonad c, LaxProfunctor sk tk kk, Ob c, Ob m) => Monad (PK (P sk tk kk (CO c) m)) where
  eta = Prof (dimapLax epsilon eta . laxId)
  mu = Prof (dimapLax delta mu . laxComp)

type ProfSq p q f g = Sq '(PK p, FUN g) '(PK q, FUN f)

-- | The collage is a cotabulator with this 2-cell.
--
-- > J-InjR-Col
-- > |   v   |
-- > p---@   |
-- > |   v   |
-- > K-InjL-Col
isCotabulator :: (Profunctor p) => ProfSq p Collage (InjR p) (InjL p)
isCotabulator = Sq $ Prof $ \(InjL f :.: p) -> f :.: InjR (L2R p) \\ p

-- | Any 2-cell of shape p(a, b) -> e(f a, g b) factors through the cotabulator 2-cell.
--
-- > J--f--H    J-Inj1-CG--X--H
-- > |  v  |    |   v   |  v  |
-- > p--@  | == p---@   |  |  |
-- > |  v  |    |   v   |  v  |
-- > K--g--H    K-Inj2-CG--X--H
type CotabulatorFactorizer :: Type -> forall (p :: j +-> k) -> (j +-> h) -> (k +-> h) -> COLLAGE p +-> h
data CotabulatorFactorizer s p f g a b where
  CF :: (Ob b) => a ~> CotabulatorFactorizer s p f g % b -> CotabulatorFactorizer s p f g a b

instance
  (Profunctor p, Representable f, Representable g, Reifies s (ProfSq p Id f g))
  => Profunctor (CotabulatorFactorizer s p f g)
  where
  dimap = dimapRep
  r \\ CF x = r \\ x
instance
  (Profunctor p, Representable f, Representable g, Reifies s (ProfSq p Id f g))
  => Representable (CotabulatorFactorizer s p f g)
  where
  type CotabulatorFactorizer s p f g % R a = f % a
  type CotabulatorFactorizer s p f g % L a = g % a
  index (CF f) = f
  tabulate f = CF f \\ f
  repMap = \case
    InL f -> repMap @g f
    InR f -> repMap @f f
    L2R p ->
      p // case reflect ([] @s) of Sq (Prof n) -> case n (tabulate @g (repMap @g (src p)) :.: p) of Id g :.: f -> index f . g

cotabulatorFactorize
  :: forall p f g r
   . (Profunctor p, Representable f, Representable g)
  => ProfSq p Id f g
  -> ( forall s
        . (Reifies s (ProfSq p Id f g))
       => ProfSq Id Id (CotabulatorFactorizer s p f g) (CotabulatorFactorizer s p f g)
       -> r
     )
  -> r
cotabulatorFactorize sq f = reify sq $ \(Proxy @s) -> f (vArr $ obj @(FUN (CotabulatorFactorizer s p f g)))