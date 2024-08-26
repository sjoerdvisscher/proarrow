module Proarrow.Category.Bicategory.Prof where

import Prelude (($))

import Proarrow.Adjunction qualified as A
import Proarrow.Category.Bicategory
  ( Adjunction (..)
  , Bicategory (..)
  , Bimodule (..)
  , Comonad (..)
  , Monad (..)
  , (==)
  , (||)
  )
import Proarrow.Category.Bicategory.Co (COK (..), Co (..))
import Proarrow.Category.Bicategory.Kan (RightKanExtension (..), RightKanLift (..))
import Proarrow.Category.Bicategory.Op (OPK (..), Op (..))
import Proarrow.Category.Bicategory.Product (PRODK (..), Prod (..))
import Proarrow.Category.Bicategory.Sub (IsOb, SUBCAT (..), Sub (..))
import Proarrow.Category.Equipment (Equipment (..), HasCompanions (..))
import Proarrow.Category.Instance.Prof ()
import Proarrow.Category.Opposite qualified as Op
import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Is
  , IsCategoryOf
  , Profunctor (..)
  , Promonad (..)
  , UN
  , arr
  , dimapDefault
  , lmap
  , obj
  , rmap
  , (//)
  , (:~>)
  , type (+->)
  )
import Proarrow.Object (src, tgt)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Ran qualified as R
import Proarrow.Profunctor.Representable (RepCostar (..), Representable (..))
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
  type Ob @(PROFK j k) p = (Is PK p, Profunctor (UN PK p))

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

type FUNK = COK (SUBCAT ProfRep PROFK)
type FUN p = CO (SUB @ProfRep (PK p))
type UNFUN p = UN PK (UN SUB (UN CO p))

instance HasCompanions PROFK FUNK where
  type Companion PROFK FUNK p = PK (UNFUN p)
  mapCompanion (Co (Sub (Prof n))) = Prof n
  compToId = Prof id
  compFromId = Prof id
  compToCompose (Co f) (Co g) = Prof id \\ f \\ g
  compFromCompose (Co f) (Co g) = Prof id \\ f \\ g

instance Equipment PROFK FUNK where
  type Conjoint PROFK FUNK p = PK (RepCostar (UNFUN p))
  mapConjoint (Co (Sub (Prof @p n))) = Prof \(RepCostar @a f) -> RepCostar (f . index (n (tabulate @p @a (repMap @p @a id))))
  conjToId = Prof (Id . unRepCostar)
  conjFromId = Prof \(Id f) -> RepCostar f \\ f
  conjToCompose (Co (Sub Prof{})) (Co (Sub (Prof @g _))) = Prof \(RepCostar @b h) -> RepCostar id :.: RepCostar h \\ repMap @g (obj @b)
  conjFromCompose (Co (Sub (Prof @f _))) (Co (Sub Prof{})) = Prof \(RepCostar f :.: RepCostar g) -> RepCostar (g . repMap @f f)

instance (Promonad p) => Monad (PK p :: PROFK k k) where
  eta = Prof (arr . unId)
  mu = Prof \(p :.: q) -> q . p

instance (Procomonad p) => Comonad (PK p :: PROFK k k) where
  epsilon = Prof (Id . extract)
  delta = Prof duplicate

instance
  (IsCategoryOf j cj, IsCategoryOf k ck, Profunctor p)
  => Bimodule (PK ck) (PK cj) (PK p :: PROFK j k)
  where
  leftAction = Prof \(f :.: p) -> lmap f p
  rightAction = Prof \(p :.: f) -> rmap f p

instance (A.Adjunction l r) => Adjunction (PK l :: PROFK c d) (PK r) where
  unit = Prof \(Id f) -> lmap f A.unit \\ f
  counit = Prof (Id . A.counit)

instance (Profunctor f, Profunctor j) => RightKanExtension (PK j :: PROFK d c) (PK f :: PROFK e c) where
  type Ran (PK j) (PK f) = PK (R.Ran (Op.OP j) f)
  ran = Prof \(j :.: r) -> R.runRan j r
  ranUniv (Prof n) = Prof \g -> g // R.Ran \j -> n (j :.: g)

instance (Profunctor f, Profunctor j) => RightKanLift (PK j :: PROFK c d) (PK f :: PROFK c e) where
  type Rift (PK j) (PK f) = PK (R.Rift (Op.OP j) f)
  rift = Prof \(r :.: j) -> R.runRift j r
  riftUniv (Prof n) = Prof \g -> g // R.Rift \j -> n (g :.: j)

-- | Hom 2-functor
type Hom :: forall {s}. forall (kk :: CAT s) -> forall {i} {j} {k} {l}. kk i j -> kk k l -> kk i k +-> kk j l
data Hom kk p q a b where
  Hom :: (Ob a, Ob b) => a `O` p ~> q `O` b -> Hom kk p q a b

instance (Bicategory kk, Ob0 kk i, Ob0 kk j, Ob0 kk k, Ob0 kk l, Ob p, Ob q) => Profunctor (Hom kk (p :: kk j i) (q :: kk k l)) where
  dimap f g (Hom sq) = Hom (f || obj @p == sq == obj @q || g) \\ f \\ g
  r \\ Hom{} = r

hom2Map :: (Bicategory kk) => PROD (OP a) b ~> PROD (OP c) d -> PK (Hom kk c b) ~> PK (Hom kk a d)
hom2Map (Prod (Op m) n) = Prof (\(Hom @_ @a @b f) -> Hom (obj @a || m == f == n || obj @b) \\\ f) \\\ m \\\ n

homId :: forall kk i. (Bicategory kk, Ob0 kk i) => PK (Id :: kk i i +-> kk i i) ~> PK (Hom kk I I)
homId = (Prof \(Id f) -> Hom (leftUnitorInv (tgt f) . f . rightUnitor (src f)) \\ f) \\ iObj @kk @i

homCompose
  :: forall {kk} {i} {j} {k} {i'} {j'} {k'} p q p' q'
   . ( Bicategory kk
     , Ob (p :: kk j k)
     , Ob (p' :: kk j' k')
     , Ob (q :: kk i j)
     , Ob (q' :: kk i' j')
     , Ob0 kk i
     , Ob0 kk j
     , Ob0 kk k
     , Ob0 kk i'
     , Ob0 kk j'
     , Ob0 kk k'
     )
  => PK (Hom kk p p') `O` PK (Hom kk q q') ~> PK (Hom kk (p `O` q) (p' `O` q'))
homCompose =
  let p = obj @p; p' = obj @p'; q = obj @q; q' = obj @q'
  in (p `o` q) // (p' `o` q') // Prof \(Hom @_ @a @b l :.: Hom @_ @_ @c r) ->
      let a = obj @a; b = obj @b; c = obj @c
      in Hom (associatorInv p' q' c . (obj @p' `o` r) . associator p' b q . (l `o` obj @q) . associatorInv a p q) \\\ r \\\ l

-- class PseudoProfunctor (p :: kk1 j1 k1 -> kk2 j2 k2 ->