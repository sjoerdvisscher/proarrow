{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Sites and sheaves.
--
-- A /cover/ of an object @a@ is a family of arrows into @a@, its /legs/, that together count as
-- all of @a@. The model is the opens of a space: an open is covered by smaller opens whose union
-- it is. A 'Site' is a category with a choice of covers, called a /coverage/.
--
-- Read an element of @p a b@ as data over @a@ (@b@ is a parameter along for the ride). Restricting
-- along a leg @g :: x '~>' a@, with @'lmap' g@, gives data over @x@. A family, one element per leg,
-- is /matching/ when its elements agree wherever two legs overlap: for legs @g@, @g'@ and any
-- @u :: z '~>' x@, @v :: z '~>' y@ with @'legArrow' g . u = 'legArrow' g' . v@,
-- @'lmap' u (m g) = 'lmap' v (m g')@. @p@ is a 'Sheaf' when every matching family is the
-- restriction of exactly one element at @a@. That rules out two failures:
--
-- * /Too many wholes./ Two distinct elements at @a@ restrict to the same family, so agreeing on
--   every leg does not make two things equal, and nothing can be proved by taking @a@ apart.
--
-- * /Too few./ A matching family is the restriction of no element at @a@, so compatible local
--   data cannot be assembled, and nothing can be built by putting @a@ together.
--
-- Neither implies the other, and counting the two sides decides neither:
--
-- @
--                                                elements at a   matching families   verdict
-- the representable at FLS, Atomic on BOOL             0                 1           too few
-- the constant presheaf, Joins on (BOOL, BOOL)         2                 1           too many
-- the collapsing presheaf, Atomic on BOOL              2                 2           not injective
-- @
--
-- Overlap is stated over every commuting square, not over /the/ pullback, so two legs need not
-- have a pullback object. 'Sums' relies on this: it works over a free category that has none.
--
-- The arrows into @a@ that factor through some leg form the /sieve/ the cover generates. Covers are
-- given by their legs because a list of legs is finite and a sieve usually is not. Sieves are the
-- truth values of presheaf categories, see "Proarrow.Profunctor.Instance.Sieve". When covers are
-- stable and compose, the coverage generates a Grothendieck topology; 'Sums' shows it need not.
--
-- Covers given by generating arrows, and gluing as an operation rather than a condition, follow
-- Arnaud Spiwack's /Sheaves in Haskell/ (Tweag, 2026, <https://www.tweag.io/blog/2026-06-18-sheaves-in-haskell/>).
-- Added here: the category, the sieves, the classifier and a decision procedure for the sheaf
-- condition, the last three in "Proarrow.Category.Enriched.Finitary.Sheaf".
module Proarrow.Category.Sheaf where

import Data.Kind (Constraint, Type)
import Data.List (subsequences, tails)
import Data.Maybe (fromMaybe, listToMaybe)
import Prelude (Bool, Maybe (..), and, error, not, null, (||))

import Proarrow.Category.Enriched.Finitary (Finitary (..), FiniteCat, LocallyFinite, factorThrough, foreachOb)
import Proarrow.Category.Enriched.Thin (Thin)
import Proarrow.Category.Instance.Free (Elem, FREE)
import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Category.Monoidal.Cartesian (Bicartesian)
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..), type (+))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (CAT, CategoryOf (..), Hom, Kind, Profunctor (..), Promonad (..), obj, rmap, (//), type (+->))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Limit.Pullback (HasPullbacks (..))
import Proarrow.Object (pattern Objs)
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), withObCorep)
import Proarrow.Profunctor.Instance.Product (fstP, sndP, (:*:) (..))
import Proarrow.Profunctor.Instance.Rift (Rift (..))
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor (..))
import Proarrow.Profunctor.Instance.Yoneda (Yo (..))

-- * Sites

-- | The kind of coverage names. A coverage is named by an empty type, the first argument of
-- 'Site', and has no values.
type Coverage :: Kind
type Coverage = Type

-- | A coverage, named @t@, on the category @k@. Several coverages can live on one category, so the
-- name is a parameter rather than a wrapper on the kind.
--
-- A cover is given by its /legs/, the arrows of the covering family. Every object is covered by
-- its identity; that cover is left implicit, and 'Cover' and 'covers' list the others. The laws are
--
-- [Stability] covers pull back: restricting a cover of @a@ to a part @b@ of @a@ gives a cover of
--   @b@. Given a cover @c@ of @a@ and any @f :: b '~>' a@, the object @b@ has a cover (possibly
--   just its identity) each of whose legs @h@ satisfies @f . h = 'legArrow' g . h'@ for some leg
--   @g@ of @c@ and some @h'@. Only the equation is asked for. No pullback object has to exist.
--
-- [Naming] a family over a cover @c@, a function @forall x. 'Leg' t k a c x -> r@ as 'glue' takes
--   and 'PulledBack' carries, is consulted only at the legs of @c@: those in @'legs' c@, or built
--   from the cover's own data. Its values at other legs are unspecified.
--
-- Naming matters when several covers share a type-level name @c@, as 'Atomic'\'s do on a category
-- that is not thin and 'Joins'\'s always do. Then 'Leg' also admits the legs of the other covers
-- with that name, so a hand-written 'glue' takes its legs from the cover it was given.
type Site :: Coverage -> Kind -> Constraint
class (CategoryOf k) => Site t k where
  -- | A cover of @a@. The type @c@ names it, so that 'Leg' can say which cover a leg belongs to;
  -- the value is the evidence that @c@ covers @a@.
  data Cover t k (a :: k) (c :: Type)

  -- | A leg of the cover @c@ of @a@, with source @x@.
  data Leg t k (a :: k) (c :: Type) (x :: k)

  -- Haddock gives no anchor to the constructors of a data family instance written inside a class
  -- instance, so each coverage below names its own in the docs of its cover tags instead.

  -- | The arrow a leg stands for.
  legArrow :: Leg t k a c x -> x ~> a

  -- | The legs of a cover.
  legs :: Cover t k a c -> [SomeLeg t k a c]

-- | A leg of the cover @c@ of @a@, with its source hidden.
type SomeLeg :: Coverage -> forall (k :: Kind) -> k -> Type -> Type
data SomeLeg t k a c where
  SomeLeg :: Leg t k a c x -> SomeLeg t k a c

-- | A site whose covers can be listed, object by object, as the law tests and the decision
-- procedure of "Proarrow.Category.Enriched.Finitary.Sheaf" need. A free category is a 'Site' but
-- not this: its 'Ob' cannot tell whether an object is a sum.
--
-- [Composition] covers compose. If @c@ covers @a@ and every leg of @c@ is itself covered, the
--   composites cover @a@ too. With Stability this makes the coverage generate a Grothendieck
--   topology, so 'Proarrow.Category.Enriched.Finitary.Sheaf.closure' is idempotent and preserves
--   meets, which 'Proarrow.Category.Enriched.Finitary.Sheaf.Plus' needs.
--   'Proarrow.Testing.Laws.testLawvereTierney' is the check.
class (Site t k) => HasFiniteCovers t k where
  -- | The covers of an object, beyond the identity.
  covers :: forall (a :: k). (Ob a) => [SomeCover t k a]

-- | A cover of @a@, with its name hidden.
type SomeCover :: Coverage -> forall (k :: Kind) -> k -> Type
data SomeCover t k a where
  SomeCover :: Cover t k a c -> SomeCover t k a

-- | How an arrow into @a@ factors through a cover of @a@: the leg it goes through, and the arrow
-- to that leg\'s source. The equation @f = 'legArrow' g . h@ is the caller\'s to rely on and the
-- instance\'s to respect.
type Factors :: Coverage -> forall (k :: Kind) -> k -> Type -> k -> Type
data Factors t k a c x where
  Factors :: Leg t k a c y -> x ~> y -> Factors t k a c x

-- | How an arrow into @a@ factors through a cover of @a@, if it does: through the first leg it
-- factors through, found by 'factorThrough'. Only the hom-sets have to be finite.
factorThroughCover :: (Site t k, LocallyFinite k) => Cover t k a c -> x ~> a -> Maybe (Factors t k a c x)
factorThroughCover c h = listToMaybe [Factors l u | SomeLeg l <- legs c, Just u <- [h // legArrow l // factorThrough h (legArrow l)]]

-- | A cover pulled back along an arrow @f :: b '~>' a@: either @f@ itself factors through a leg
-- (the pullback is @b@\'s implicit identity cover), or some cover of @b@ has every leg factoring
-- through one.
type PulledBack :: Coverage -> forall (k :: Kind) -> k -> Type -> k -> Type
data PulledBack t k a c b where
  AlreadyFactors :: Factors t k a c b -> PulledBack t k a c b
  PulledBack :: Cover t k b c' -> (forall x. Leg t k b c' x -> Factors t k a c x) -> PulledBack t k a c b

-- | 'Site'\'s Stability law as an /operation/: a pullback one can compute with, carrying the
-- factorisation of each new leg through an old one. It lets a sheaf be glued structurally. Without
-- it, gluing into a carrier with no 'glue' of its own (an internal hom, the closed sieves) means
-- searching the carrier\'s elements ('Proarrow.Category.Enriched.Finitary.Topos.glueBySearch'),
-- which needs the carrier to be finitary.
--
-- Separate from 'Site' because 'Sums' cannot implement it: a free bicartesian category is not
-- extensive, so its covers do not pull back.
class (Site t k) => StableSite t k where
  pullbackCover :: (Ob b) => Cover t k a c -> b ~> a -> PulledBack t k a c b

-- | A cover pulled back along the identity of the object it covers: itself, each leg factoring
-- through itself. Every instance needs this clause, and this version cannot get it wrong. In a
-- hand-written one, naming another leg with the same source type-checks.
pullbackAlongId :: (Site t k) => Cover t k a c -> PulledBack t k a c a
pullbackAlongId c = PulledBack c \l -> legArrow l // Factors l id

-- * Sheaves

-- | A profunctor that is a sheaf for the coverage @t@ on its contravariant side: every matching
-- family over a cover glues to one element. A family @m@ over the legs of a cover @c@ is
-- /matching/ when it agrees on overlaps: for legs @g@, @g'@ and any @u :: z '~>' x@,
-- @v :: z '~>' y@ with @'legArrow' g . u = 'legArrow' g' . v@, @'lmap' u (m g) = 'lmap' v (m g')@.
-- 'Sums' below is the smallest worked instance. The laws are
--
-- [Restriction] for matching @m@, @'lmap' ('legArrow' g) ('glue' c m) = m g@ at every leg @g@ of
--   @c@: the gluing restricts back to the family;
--
-- [Uniqueness] @'glue' c (\\g -> 'lmap' ('legArrow' g) x) = x@: an element is the gluing of its
--   own restrictions.
--
-- Together they make restriction a bijection from the elements at @a@ to the matching families on
-- @c@. On a non-matching family 'glue' is unspecified. The 'Sums' instance keeps one leg's
-- covariant component and drops the other, which is sound only because matching forces them equal.
--
-- @p@ is a sheaf when each presheaf @p (-) b@ is one, and 'glue' is stated for every @b@ at once.
-- A cosheaf, gluing on the covariant side, is a
-- @'Sheaf' t ('Proarrow.Category.Instance.Opposite.Op' p)@ for a coverage on @'OPPOSITE' k@. The
-- library defines no such coverage.
--
-- Instances are indexed by the shape of the profunctor: the limits below, a site's
-- representables, and the image of sheafification. An instance per coverage would overlap all of
-- them, so 'Trivial' gets the function 'glueTrivial' instead.
type Sheaf :: forall {j} {k}. Coverage -> j +-> k -> Constraint
class (Site t k, Profunctor p) => Sheaf t (p :: j +-> k) where
  glue
    :: forall (a :: k) c (b :: j)
     . (Ob a, Ob b)
    => Cover t k a c
    -> (forall x. Leg t k a c x -> p x b)
    -> p a b

-- | The limits of profunctors are sheaves whenever their factors are: the terminal profunctor for
-- every coverage, and a product of sheaves glued componentwise.
instance (Site t k, CategoryOf j) => Sheaf t (TerminalProfunctor :: j +-> k) where
  glue _ _ = TerminalProfunctor

instance (Sheaf t p, Sheaf t q) => Sheaf t (p :*: q) where
  glue c m = glue @t c (\g -> fstP (m g)) :*: glue @t c (\g -> sndP (m g))

-- * Coverages

-- | The trivial coverage: only identities cover, so every profunctor is a sheaf.
type Trivial :: Coverage
type data Trivial

instance (CategoryOf k) => Site Trivial k where
  data Cover Trivial k a c
  data Leg Trivial k a c x
  legArrow g = case g of {}
  legs c = case c of {}

instance (CategoryOf k) => HasFiniteCovers Trivial k where
  covers = []

instance (CategoryOf k) => StableSite Trivial k where
  pullbackCover c _ = case c of {}

-- | Every profunctor is a sheaf for 'Trivial', by the eliminator of an empty 'Cover'. This is a
-- function rather than an @instance 'Sheaf' 'Trivial' p@ because that head and the two closure
-- instances above overlap (at @'Sheaf' 'Trivial' 'TerminalProfunctor'@, say) with neither more
-- specific than the other, so GHC could not choose between them. Write @glue = glueTrivial@ to get
-- the instance for one profunctor.
glueTrivial :: Cover Trivial k a c -> (forall x. Leg Trivial k a c x -> p x b) -> p a b
glueTrivial c _ = case c of {}

-- | The atomic coverage: every single arrow into an object covers it. So a sieve is covering iff it
-- is nonempty (the /atomic/ topology, with 'HasPullbacks' as its Ore condition). A sheaf is a
-- profunctor whose restriction along every arrow is a bijection. On a chain that is a presheaf
-- that is constant up to iso.
--
-- Stability is the pullback square: pulling a leg back along an arrow into its target gives the
-- cover of that arrow's source by the pullback projection, and the other projection factors it
-- through the old leg. Covers compose, since a composite of single arrows is a single arrow. This
-- is the first coverage here whose legs are themselves covered, so it is the first to exercise
-- 'HasFiniteCovers'\'s Composition law.
--
-- The identity is listed as a cover too. It decides nothing new, and dropping it would take
-- deciding @b ~ a@ under 'foreachOb', which a coverage generic in @k@ cannot do.
type Atomic :: Coverage
type data Atomic

-- | The name of the 'Atomic' cover of an object by a single arrow out of @b@: the 'Cover'
-- constructor is @Solely@ and its one 'Leg' constructor is @Only@. Two distinct arrows @b '~>' a@
-- share the name, so the name is not a singleton, and 'Site'\'s Naming law makes that
-- harmless: 'pullbackCover' answers for the leg of the cover it built, and says nothing true about
-- an @Only@ built from another arrow. On a thin category the arrow is unique and the name a
-- singleton after all.
type data Along (b :: k)

instance (HasPullbacks k, FiniteCat k) => Site Atomic k where
  data Cover Atomic k a c where
    Solely :: (Ob b) => b ~> a -> Cover Atomic k a (Along b)
  data Leg Atomic k a c x where
    Only :: (Ob b) => b ~> a -> Leg Atomic k a (Along b) b
  legArrow (Only f) = f
  legs (Solely f) = [SomeLeg (Only f)]

instance (HasPullbacks k, FiniteCat k) => HasFiniteCovers Atomic k where
  covers @a = foreachOb @k \ @b -> [SomeCover (Solely f) | f <- elements @(Hom k) @b @a]

instance (HasPullbacks k, FiniteCat k) => StableSite Atomic k where
  pullbackCover (Solely f) g = pullback f g \p1 p2 -> p1 // PulledBack (Solely p2) \(Only _) -> Factors (Only f) p1

-- | The open-cover coverage of a finite distributive lattice: an object is covered by any family of
-- objects below it whose join it is. Read the lattice as the opens of a finite space and its
-- sheaves are the sheaves on that space: a section over an open is determined by, and assembled
-- from, its sections over any opens that cover it. On @(BOOL, BOOL)@, the opens of the discrete
-- two-point space (see "Proarrow.Category.Instance.Product"), the whole space is covered by its
-- two points.
--
-- The empty family covers the bottom, the join of nothing, so a sheaf has exactly one section over
-- the bottom, as over the empty set. On a chain nothing else is covered.
--
-- 'covers' lists the antichains strictly below an object that join to it, found by enumerating
-- subsets, so it is for small lattices only. Other families generate the same sieves.
--
-- The instances ask for 'Proarrow.Category.Monoidal.Cartesian.Bicartesian' (meet is the product,
-- join the coproduct) and 'Thin', so that "is there an arrow" reads as @<=@.
-- 'Proarrow.Category.Instance.FinSet.FINSET' is bicartesian and distributive but not thin, and this
-- coverage would mean nothing there. Distributivity gives stability: pulled back along
-- @b '<=' a@, a cover @{x_i}@ of @a@ becomes @{b '&&' x_i}@, whose join is @b@. Covers compose,
-- since a join of joins is a join. The topology is subcanonical (representable presheaves are
-- sheaves), but a two-sided @'Yo' a ('OP' b)@ need not be one: the empty cover asks for one
-- element at the bottom for every object of @j@, and it has none at an object @b@ has no arrow to.
--
-- The finite, stable counterpart of 'Sums': a distributive lattice is the thin case of the
-- extensivity that a free bicartesian category lacks.
type Joins :: Coverage
type data Joins

-- | The name of every 'Joins' cover: the 'Cover' constructor is @ByJoin@, holding its legs, and
-- the 'Leg' constructor is @Under@, one per member of the family. A @ByJoin@ is a cover of @a@
-- only when its legs join to @a@; 'covers' lists exactly the antichains that do. All the covers
-- of an object share the name, so 'Site'\'s Naming law matters here: a family over
-- one of them is not asked about the legs of another.
type data Join

instance (Thin k, FiniteCat k, Bicartesian k) => Site Joins k where
  data Cover Joins k a c where
    ByJoin :: [SomeLeg Joins k a Join] -> Cover Joins k a Join
  data Leg Joins k a c x where
    Under :: (Ob x) => x ~> a -> Leg Joins k a Join x
  legArrow (Under f) = f
  legs (ByJoin ls) = ls

instance (Thin k, FiniteCat k, Bicartesian k) => HasFiniteCovers Joins k where
  covers @a = [SomeCover (ByJoin ls) | ls <- subsequences strictlyBelow, isAntichain ls, isJoin ls]
    where
      strictlyBelow :: [SomeLeg Joins k a Join]
      strictlyBelow = foreachOb @k \ @x -> [SomeLeg (Under f) | not (sourceBelow (obj @a) (obj @x)), f <- elements @(Hom k) @x @a]
      isAntichain ls = and [not (legBelow l m || legBelow m l) | l : ms <- tails ls, m <- ms]
      -- @a@ is below the join of the family, which is below @a@ by construction
      isJoin ls = joinOf ls (sourceBelow (obj @a))

instance (Thin k, FiniteCat k, Bicartesian k) => StableSite Joins k where
  pullbackCover c@(ByJoin ls) f = pullbackJoin c ls f

-- | Whether the source of the first arrow is below that of the second: in a thin category,
-- whether there is an arrow between them at all.
sourceBelow :: forall {k} (x :: k) (y :: k) a b. (FiniteCat k) => x ~> a -> y ~> b -> Bool
sourceBelow f g = f // g // not (null (elements @(Hom k) @x @y))

-- | Whether one leg's source is below the other's.
legBelow :: (FiniteCat k) => SomeLeg Joins k a Join -> SomeLeg Joins k a Join -> Bool
legBelow (SomeLeg (Under f)) (SomeLeg (Under g)) = sourceBelow f g

-- | The join of the legs' sources, as the arrow it has into their common target: the copairing
-- of the legs, starting from the initial object.
joinOf
  :: forall {k} (a :: k) r
   . (HasBinaryCoproducts k, HasInitialObject k, Ob a)
  => [SomeLeg Joins k a Join]
  -> (forall j. j ~> a -> r)
  -> r
joinOf [] kont = kont (initiate @k @a)
joinOf (SomeLeg (Under f) : ls) kont = joinOf ls (copair f)
  where
    copair :: forall x j. x ~> a -> j ~> a -> r
    copair g h = g // h // withObCoprod @k @x @j (kont (g ||| h))

-- | 'Joins'\'s Stability: the meets of the source with the legs. Each is below its leg, so the
-- factorisation is found by 'factorThroughCover'; it is recomputed per leg rather than carried,
-- as a leg is only its arrow. The search fails only for a leg of some other cover of @b@, which
-- 'Site'\'s Naming law rules out.
pullbackJoin
  :: forall {k} (b :: k) a
   . (Thin k, FiniteCat k, Bicartesian k, Ob b)
  => Cover Joins k a Join
  -> [SomeLeg Joins k a Join]
  -> b ~> a
  -> PulledBack Joins k a Join b
pullbackJoin c ls f = PulledBack (ByJoin [meet g | SomeLeg (Under g) <- ls]) \(Under h) ->
  fromMaybe (error "pullbackJoin: not a leg of the pulled-back cover (Site's Naming law)") (factorThroughCover c (f . h))
  where
    meet :: forall x. (Ob x) => x ~> a -> SomeLeg Joins k b Join
    meet _ = withObProd @k @b @x (SomeLeg (Under (fst @k @b @x)))

-- | The sum coverage on a free category with binary coproducts: a sum is covered by its two
-- injections. This is the syntactic site of Spiwack's post (see the module header). In the free
-- bicartesian closed category 'Proarrow.Tools.CCC.Syntax', the booleans @TermF '+' TermF@ are
-- covered by @true@ and @false@.
--
-- Read @p a@ as the ways of producing an @a@. Being a sheaf means @p Bool ≅ p TermF × p TermF@:
-- every pair of branches has a conditional, and only one. With too many, a proof by cases
-- establishes nothing. With too few, @if-then-else@ is not definable. On a representable the
-- conditional is @'|||'@, which is why 'glue' below is @[t, e]@. The conditional on a test
-- @f :: c '~>' Bool@ is 'Proarrow.Tools.CCC.either', which needs the distributive law as well.
--
-- __Stability does not hold.__ It would need every arrow into a sum to split its source into a
-- sum (/extensivity/), and a free bicartesian category is not extensive. The restriction of
-- @id '|||' 'lft' :: (u '+' u) '+' u ~> u '+' u@ to the left summand is @id@, which factors
-- through neither injection. With a richer constraint list,
-- @'Proarrow.Monoid.mempty' :: UnitF ~> u '+' u@ has a source that is not a sum at all.
-- So the coverage generates no Grothendieck topology. Nothing here relies on stability: 'glue'\'s
-- laws are the coproduct's universal property, and @FREE@ cannot list the covers of an arbitrary
-- object, so it is not a 'HasFiniteCovers' and the topology machinery never runs at it.
type Sums :: Coverage
type data Sums

-- | The name of the cover of @x '+' y@ by its injections, whose 'Cover' constructor is
-- @BySummands@ and whose 'Leg' constructors are @AtLeft@ and @AtRight@.
type Summands :: k -> k -> Type
type data Summands x y

instance (HasBinaryCoproducts `Elem` cs) => Site Sums (FREE cs (p :: CAT k)) where
  data Cover Sums (FREE cs p) a c where
    BySummands :: (Ob x, Ob y) => Cover Sums (FREE cs p) (x + y) (Summands x y)
  data Leg Sums (FREE cs p) a c z where
    AtLeft :: (Ob x, Ob y) => Leg Sums (FREE cs p) (x + y) (Summands x y) x
    AtRight :: (Ob x, Ob y) => Leg Sums (FREE cs p) (x + y) (Summands x y) y
  legArrow AtLeft = lft
  legArrow AtRight = rgt
  legs BySummands = [SomeLeg AtLeft, SomeLeg AtRight]

-- | Sums are colimits, so the representables are sheaves for 'Sums': gluing is @'|||'@ on the
-- contravariant component.
--
-- The initial object is needed too. An element of @'Yo' x ('OP' b)@ also has a covariant
-- component @b '~>' d@. A family over the two injections has one per leg, and the glued element
-- only one. Matching forces the two to agree because the injections overlap at the initial object,
-- @'lft' . initiate = 'rgt' . initiate@. Without it every family matches vacuously, and
-- restriction fails for any @j@ with a hom-set bigger than one.
instance
  (HasBinaryCoproducts `Elem` cs, HasInitialObject `Elem` cs, CategoryOf j)
  => Sheaf Sums (Yo (x :: FREE cs (p :: CAT k)) (OP (b :: j)) :: j +-> FREE cs p)
  where
  glue BySummands m = case (m AtLeft, m AtRight) of
    (Yo f h, Yo g _) -> Yo (f ||| g) h

-- | __The coverage by the image of a functor.__ A 'Corepresentable' @w@ is a functor
-- @F = w '%%' -@ from @k@ to @j@, with @w d c ≅ F d ~> c@. Every object @c@ of @j@ is covered by all
-- the arrows into it from the image, @F d ~> c@, so a leg is an element of @w@. For an object in the
-- image the cover contains its identity and asks nothing.
--
-- It is stable, since pulling a leg back along @g@ is composing with @g@, and the covers compose,
-- since the cover of a leg's source is again an image cover, and contains that source's identity.
-- A presheaf on @k@ extends to a sheaf on @j@: its right Kan lift @q '<|' w@ ('Rift'), whose value
-- at @c@ is a family over all the arrows @F d ~> c@. The restriction of a sheaf back to @k@ is
-- @w ':.:' s@, and the two are adjoint by the
-- 'Proarrow.Profunctor.Corepresentable.Corepresentable' instance of @'Star' ('Rift' ('OP' w))@.
--
-- The comparison lemma needs @F@ to be fully faithful: 'corepMap' is a bijection on each hom-set,
-- equivalently @('~>') ≅ w '|>' w@ ('Proarrow.Testing.Laws.testRanFullyFaithful'). Then the unit
-- of the adjunction is an isomorphism exactly on the sheaves, the counit is an isomorphism, and
-- the sheaves are the presheaves on @k@. Without it the coverage is still lawful, but its sheaves
-- are the presheaves on the full subcategory of @j@ on the objects @F d@. When @F@ sends two
-- objects to one, every presheaf is a sheaf, and the unit is a diagonal.
--
-- Two examples: the left inclusion of a collage, whose other objects are covered by the arrows
-- from the left layer, and the edges of a graph, covering each vertex by the two ends of an edge.
type ByImage :: forall {j} {k}. (j +-> k) -> Coverage
type data ByImage w

-- | The name of the one 'ByImage' cover of an object, whose 'Cover' constructor is @Images@ and
-- whose 'Leg' constructor is @FromImage@, one leg per element of @w@.
type data Image

instance (Corepresentable w, Finitary w, FiniteCat k) => Site (ByImage (w :: j +-> k)) j where
  data Cover (ByImage w) j a c where
    Images :: (Ob a) => Cover (ByImage w) j a Image
  data Leg (ByImage w) j a c x where
    FromImage :: (Ob d) => w d a -> Leg (ByImage w) j a Image (w %% d)
  legArrow (FromImage x) = coindex x
  legs @a Images = foreachOb @k \ @d -> [SomeLeg (FromImage x) | x <- elements @w @d @a]

instance (Corepresentable w, Finitary w, FiniteCat k) => HasFiniteCovers (ByImage (w :: j +-> k)) j where
  covers = [SomeCover Images]

instance (Corepresentable w, Finitary w, FiniteCat k) => StableSite (ByImage (w :: j +-> k)) j where
  pullbackCover Images g = PulledBack Images \(FromImage (x :: w d b)) -> withObCorep @w @d (Factors (FromImage (rmap g x)) id)

-- | The extension of a presheaf along @w@ is a sheaf: gluing reads each leg's family at the
-- identity of its source.
instance
  (Corepresentable w, Finitary w, FiniteCat k, Profunctor q)
  => Sheaf (ByImage (w :: j +-> k)) (Rift (OP w) q :: i +-> j)
  where
  glue Images m = Rift \(x :: w d a) -> x // case m (FromImage x) of Rift f -> f (corepUniv @w @d)

-- | __The coverage induced along a functor.__ For a coverage @t@ on @j@ and a functor
-- @F = w '%%' -@ from @k@ to @j@, a cover of @d@ is a @t@-cover @c@ of @F d@, and its legs are
-- all the arrows @h :: e ~> d@ whose image @F h@ factors through a leg of @c@.
--
-- The comparison lemma: when @F@ is fully faithful and every object of @j@ is covered by arrows
-- out of the image ('Proarrow.Testing.Laws.testCoveredByImage'), the sheaves for @t@ are the
-- sheaves for @'Induced' t w@. Restriction is @w ':.:' s@ and extension is the
-- right Kan lift @q '<|' w@, glued by 'glueExtension', the adjunction of 'ByImage'. 'ByImage' is
-- the case where @t@ has only the image covers. Then every induced cover contains an identity,
-- and every presheaf on @k@ is a sheaf.
--
-- The opens of a space and a basis of it are the standard example: sheaves on the space are
-- sheaves on the basis.
type Induced :: forall {j} {k}. Coverage -> (j +-> k) -> Coverage
type data Induced t w

instance (Site t j, Corepresentable w, LocallyFinite j, FiniteCat k) => Site (Induced t (w :: j +-> k)) k where
  data Cover (Induced t w) k d c where
    Induce :: (Ob d) => Cover t j (w %% d) c -> Cover (Induced t w) k d c
  data Leg (Induced t w) k d c e where
    Induces :: (Ob e) => e ~> d -> Factors t j (w %% d) c (w %% e) -> Leg (Induced t w) k d c e
  legArrow (Induces h _) = h
  legs @d (Induce c) =
    foreachOb @k \ @e ->
      [SomeLeg (Induces h fs) | h <- elements @(Hom k) @e @d, Just fs <- [factorThroughCover c (corepMap @w h)]]

instance (HasFiniteCovers t j, Corepresentable w, LocallyFinite j, FiniteCat k) => HasFiniteCovers (Induced t (w :: j +-> k)) k where
  covers @d = withObCorep @w @d [SomeCover (Induce c) | SomeCover c <- covers @t @j @(w %% d)]

-- | Pulling back along @h'@ is pulling the cover of @F d@ back along @F h'@.
instance (StableSite t j, Corepresentable w, LocallyFinite j, FiniteCat k) => StableSite (Induced t (w :: j +-> k)) k where
  pullbackCover @d' (Induce c) h' =
    withObCorep @w @d'
      ( case pullbackCover c (corepMap @w h') of
          AlreadyFactors fs -> AlreadyFactors (Factors (Induces h' fs) id)
          PulledBack c' fs -> PulledBack (Induce c') \(Induces h (Factors l' u)) -> case fs l' of
            Factors l u' -> Factors (Induces (h' . h) (Factors l (u' . u))) id
      )

-- | The extension of a sheaf for the induced coverage is a sheaf for @t@. Its value at @x :: F e ~> a@
-- is found by pulling the cover back along @x@ and gluing in @q@ over the induced cover of @e@.
--
-- A function instead of an instance, because an instance would overlap the 'ByImage' one.
glueExtension
  :: forall t {i} {j} {k} (w :: j +-> k) (q :: i +-> k) (a :: j) c (b :: i)
   . (StableSite t j, Corepresentable w, LocallyFinite j, FiniteCat k, Sheaf (Induced t w) q, Ob a, Ob b)
  => Cover t j a c
  -> (forall x. Leg t j a c x -> Rift (OP w) q x b)
  -> Rift (OP w) q a b
glueExtension c m = Rift \(x@Objs :: w e a) ->
  withObCorep @w @e
    ( case pullbackCover c (coindex x) of
        AlreadyFactors (Factors l u) -> at l (rmap u (corepUniv @w @e))
        PulledBack c' fs -> glue @(Induced t w) (Induce c') \(Induces _ (Factors l' u)) -> case fs l' of
          Factors l u' -> at l (rmap (u' . u) corepUniv)
    )
  where
    at :: Leg t j a c y -> w e' y -> q e' b
    at l y = case m l of Rift f -> f y
