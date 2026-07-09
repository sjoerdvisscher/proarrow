{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Enriched where

import Data.Kind (Constraint, Type)

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Enriched.Thin (CodiscreteProfunctor (..), Thin, ThinProfunctor (..))
import Proarrow.Category.Instance.Constraint (CONSTRAINT (..), (:-) (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), leftUnitorInvWith, rightUnitorInvWith)
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (Any, CAT, CategoryOf (..), Hom, Kind, Profunctor ((\\)), Promonad (..), type (+->))
import Proarrow.Monoid (MONOIDK (..), Mon (..), Monoid (..))
import Proarrow.Object.Exponential (uncurry)
import Proarrow.Object.Exponential qualified as E
import Proarrow.Profunctor qualified as P

-- | Working with enriched categories and profunctors in Haskell is hard.
-- Instead we encode them using the underlying regular category/profunctor,
-- and show that the enriched structure can be recovered.
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
instance (Monoid (m :: k)) => EnrichedProfunctor (Clone k) (Mon :: CAT (MONOIDK (m :: k))) where
  type ProObj (Clone k) (Mon :: CAT (MONOIDK m)) M M = SUB m
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
  rmap = uncurry P.rmap
  lmap = uncurry P.lmap

instance (DaggerProfunctor p) => EnrichedProfunctor (Type, Type) p where
  type ProObj (Type, Type) p a b = '(p a b, p b a)
  withProObj r = r
  underlying p = (\() -> p) :**: (\() -> dagger p)
  enriched (f :**: _) = f ()
  rmap = uncurry P.rmap :**: uncurry P.lmap
  lmap = uncurry P.lmap :**: uncurry P.rmap

instance (ThinProfunctor p, Thin j, Thin k) => EnrichedProfunctor CONSTRAINT (p :: j +-> k) where
  type ProObj CONSTRAINT p a b = CNSTRNT (HasArrow p a b)
  withProObj r = r
  underlying p = Entails (\r -> withArr p r)
  enriched (Entails f) = f arr
  rmap @a @b @c = Entails (withArr @p (P.rmap (arr @(~>) @b @c) (arr @p @a @b)))
  lmap @a @b @c = Entails (withArr @p (P.lmap (arr @(~>) @c @a) (arr @p @a @b)))

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
