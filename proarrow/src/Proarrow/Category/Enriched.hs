{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Categories and profunctors enriched in a monoidal category @v@, encoded via their underlying
-- ordinary category\/profunctor: 'EnrichedProfunctor' equips a regular profunctor with hom-objects
-- @'ProObj' v p a b@ in @v@ from which the enriched structure is recovered, and a category is
-- 'Enriched' when its hom-profunctor is. Instances include the self-enrichment of a
-- 'Proarrow.Category.Monoidal.Closed.Closed' category.
module Proarrow.Category.Enriched where

import Data.Kind (Constraint, Type)

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Enriched.Finitary (Elt (..), Finitary, LocallyFinite)
import Proarrow.Category.Enriched.Thin
  ( CodiscreteProfunctor (..)
  , Decidable
  , DecidableProfunctor (..)
  , Decision (..)
  , Thin
  , ThinProfunctor (..)
  )
import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..))
import Proarrow.Category.Instance.Constraint (CONSTRAINT (..), (:-) (..))
import Proarrow.Category.Instance.FinHask (FINHASK (..))
import Proarrow.Category.Instance.FinHask qualified as F
import Proarrow.Category.Instance.Monoid (MONOID (..), Mon (..))
import Proarrow.Category.Instance.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof)
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), SymMonoidal (..), leftUnitorInvWith, rightUnitorInvWith)
import Proarrow.Category.Monoidal.Closed qualified as E
import Proarrow.Core (Any, CAT, CategoryOf (..), Hom, Kind, Profunctor ((\\)), Promonad (..), type (+->))
import Proarrow.Core qualified as P
import Proarrow.Limit.BinaryProduct (PROD, Prod)
import Proarrow.Monoid (Monoid (..))
import Proarrow.Profunctor.Instance.Exponential ()

-- | Working with enriched categories and profunctors in Haskell is hard.
-- Instead we encode them using the underlying regular category/profunctor,
-- and show that the enriched structure can be recovered.
--
-- Call an arrow @'Unit' '~>' x@ an /element/ of @x@. The laws say that the elements of
-- @'ProObj' v p a b@ are those of the hom-set @p a b@, and that its two actions are the
-- profunctor's:
--
-- [Elements] 'underlying' and 'enriched' are mutually inverse, so 'underlying' is a bijection from
-- @p a b@ onto the elements of @'ProObj' v p a b@.
--
-- [Right action] for @f :: b '~>' c@ in @j@ and @x :: p a b@, where @'underlying' f@ names @f@ as
-- an element of @'HomObj' v b c@:
--
-- > rmap . (underlying f ** underlying x) . leftUnitorInv == underlying (P.rmap f x)
--
-- [Left action] dually, for @g :: c '~>' a@ in @k@:
--
-- > lmap . (underlying g ** underlying x) . leftUnitorInv == underlying (P.lmap g x)
--
-- These fix 'rmap' and 'lmap' completely iff @v@ is well-pointed, as 'Type' and the thin @v@s are.
-- Functoriality follows from the 'Profunctor' instance. At @p ~ 'Hom' k@ the right-action law says
-- that the enriched composition 'comp' is @('.')@.
type EnrichedProfunctor :: forall {j} {k}. Kind -> j +-> k -> Constraint
class (Monoidal v, Profunctor p, Enriched v j, Enriched v k) => EnrichedProfunctor v (p :: j +-> k) where
  type ProObj v (p :: j +-> k) (a :: k) (b :: j) :: v
  withProObj :: (Ob (a :: k), Ob b) => ((Ob (ProObj v p a b)) => r) -> r
  underlying :: p a b -> Unit ~> ProObj v p a b
  enriched :: (Ob a, Ob b) => Unit ~> ProObj v p a b -> p a b
  rmap :: (Ob a, Ob b, Ob c) => HomObj v b c ** ProObj v p a b ~> ProObj v p a c
  lmap :: (Ob a, Ob b, Ob c) => HomObj v c a ** ProObj v p a b ~> ProObj v p c b

class (EnrichedProfunctor v (Hom k)) => Enriched v k
instance (EnrichedProfunctor v (Hom k)) => Enriched v k

type HomObj v (a :: k) (b :: k) = ProObj v (Hom k) a b

comp :: forall {k} v (a :: k) b c. (Enriched v k, Ob a, Ob b, Ob c) => HomObj v b c ** HomObj v a b ~> HomObj v a c
comp = rmap @v @(Hom k) @a @b @c

-- | Closed monoidal categories are enriched in themselves.
type HomSelf a b = a E.~~> b

underlyingSelf :: (E.Closed k) => (a :: k) ~> b -> Unit ~> HomSelf a b
underlyingSelf = E.mkExponential

enrichedSelf :: (E.Closed k, Ob (a :: k), Ob b) => Unit ~> HomSelf a b -> a ~> b
enrichedSelf = E.lower

compSelf :: forall {k} (a :: k) b c. (E.Closed k, Ob a, Ob b, Ob c) => HomSelf b c ** HomSelf a b ~> HomSelf a c
compSelf = E.comp @a @b @c

-- abusing SUBCAT Any as a cheap wrapper to prevent overlapping instances
type Clone k = SUBCAT (Any :: k -> Constraint)

-- | A monoid is a one object enriched category.
instance (Monoid (m :: k)) => EnrichedProfunctor (Clone k) (Mon :: CAT (MONOID (m :: k))) where
  type ProObj (Clone k) (Mon :: CAT (MONOID m)) M M = SUB m
  withProObj r = r
  underlying (Mon f) = Sub f
  enriched (Sub f) = Mon f
  rmap = Sub mappend
  lmap = Sub mappend

instance (Profunctor p) => EnrichedProfunctor Type p where
  type ProObj Type p a b = p a b
  withProObj r = r
  underlying p () = p
  enriched f = f ()
  rmap = E.uncurry P.rmap
  lmap = E.uncurry P.lmap

instance (DaggerProfunctor p) => EnrichedProfunctor (Type, Type) p where
  type ProObj (Type, Type) p a b = '(p a b, p b a)
  withProObj r = r
  underlying p = (\() -> p) :**: (\() -> dagger p)
  enriched (f :**: _) = f ()
  rmap = E.uncurry P.rmap :**: E.uncurry P.lmap
  lmap = E.uncurry P.lmap :**: E.uncurry P.rmap

instance (ThinProfunctor p, Thin j, Thin k) => EnrichedProfunctor CONSTRAINT (p :: j +-> k) where
  type ProObj CONSTRAINT p a b = CNSTRNT (HasArrow p a b)
  withProObj r = r
  underlying p = Entails \r -> withArr p r
  enriched (Entails f) = f arr
  rmap @a @b @c = Entails \r -> withArr @p (P.rmap (arr @(~>) @b @c) (arr @p @a @b)) r
  lmap @a @b @c = Entails \r -> withArr @p (P.lmap (arr @(~>) @c @a) (arr @p @a @b)) r

-- | A decidable thin profunctor is a profunctor enriched in the walking arrow: its hom-object is the
-- type-level 'Holds', an element of it is an arrow, and composition is conjunction.
instance (DecidableProfunctor p, Decidable j, Decidable k) => EnrichedProfunctor BOOL (p :: j +-> k) where
  type ProObj BOOL p a b = Holds p a b
  withProObj @a @b r = case decide @p @a @b of
    Yes _ -> r
    No -> r
  underlying p = toHolds p Tru
  enriched @a @b f = case decide @p @a @b of
    Yes x -> x
    No -> case f of {}
  rmap @a @b @c = case (decide @(Hom j) @b @c, decide @p @a @b) of
    (Yes g, Yes x) -> toHolds (P.rmap g x) Tru
    (No, _) -> fromFls (decide @p @a @c)
    (Yes _, No) -> fromFls (decide @p @a @c)
  lmap @a @b @c = case (decide @(Hom k) @c @a, decide @p @a @b) of
    (Yes g, Yes x) -> toHolds (P.lmap g x) Tru
    (No, _) -> fromFls (decide @p @c @b)
    (Yes _, No) -> fromFls (decide @p @c @b)

-- | @FLS@ is initial, and a decision tells us which object we are aiming at.
fromFls :: Decision p a b h -> Booleans FLS h
fromFls (Yes _) = F2T
fromFls No = Fls

-- | __A finitary profunctor is a profunctor enriched in finite sets.__ The hom-object is the
-- hom-set itself, which 'Elt' makes an object of 'FINHASK' out of nothing but the numbering, and the
-- whiskerings are the two 'dimap's.
instance (Finitary p, LocallyFinite j, LocallyFinite k) => EnrichedProfunctor FINHASK (p :: j +-> k) where
  type ProObj FINHASK p a b = FH (Elt p a b)
  withProObj r = r
  underlying x = F.arr (\() -> Elt x) \\ x
  enriched f = unElt (f F.! ())
  rmap @a = F.arr \(Elt g, Elt x) -> Elt (P.dimap (id @_ @a) g x)
  lmap @_ @b = F.arr \(Elt g, Elt x) -> Elt (P.dimap g (id @_ @b) x)

-- | The category of profunctors is enriched in itself: the hom-object is the internal hom
-- @p ':~>:' q@, an element of it is a natural transformation, and composition is the internal one.
-- Cartesian closed, hence the 'PROD' wrapper (@j '+->' k@\'s own tensor is Day convolution).
--
-- This self-enrichment is written the generic way, from 'HomSelf' and friends. Those apply to any
-- 'Closed' 'SymMonoidal' kind that has no enrichment instance of its own covering its
-- hom-profunctor.
instance (CategoryOf j, CategoryOf k) => EnrichedProfunctor (PROD (j +-> k)) (Prod (Prof :: CAT (j +-> k))) where
  type ProObj (PROD (j +-> k)) (Prod (Prof :: CAT (j +-> k))) p q = HomSelf p q
  withProObj r = r
  underlying = underlyingSelf
  enriched = enrichedSelf
  rmap = compSelf
  lmap = compSelf . swap

instance (CodiscreteProfunctor p) => EnrichedProfunctor () p where
  type ProObj () p a b = '()
  withProObj r = r
  underlying _ = U.Unit
  enriched U.Unit = anyArr
  rmap = U.Unit
  lmap = U.Unit

instance (EnrichedProfunctor v p) => EnrichedProfunctor (Clone v) (Op p) where
  type ProObj (Clone v) (Op p) (OP a) (OP b) = SUB (ProObj v p b a)
  withProObj @(OP a) @(OP b) r = withProObj @v @p @b @a r
  underlying (Op f) = Sub (underlying @v @p f)
  enriched (Sub f) = Op (enriched f)
  rmap @(OP a) @(OP b) @(OP c) = Sub (lmap @v @p @b @a @c)
  lmap @(OP a) @(OP b) @(OP c) = Sub (rmap @v @p @b @a @c)

-- | A generalized arrow of an enriched category. If @k@ is both powered and copowered, this is an adjunction.
type GenArrow :: OPPOSITE v -> k +-> k
data GenArrow n a b where
  GenArrow :: (Ob a, Ob b) => n ~> HomObj v a b -> GenArrow (OP n) a b

instance (Ob (n :: v), Enriched v k, CategoryOf k) => Profunctor (GenArrow (OP n) :: k +-> k) where
  dimap @c @a @b @d l r (GenArrow f) =
    GenArrow
      ( let g = comp @v @c @a @b . rightUnitorInvWith (underlying @v l) . f
        in comp @v @c @b @d . leftUnitorInvWith (underlying @v r) . g \\ g
      )
      \\ f
      \\ l
      \\ r
  r \\ GenArrow f = r \\ f
