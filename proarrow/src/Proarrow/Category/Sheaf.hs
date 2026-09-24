{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Sites and sheaves. A 'Site' is a category with a /coverage/: for each object, the families of
-- arrows into it that count as covering it, each given by its /legs/. A profunctor is a 'Sheaf'
-- for the coverage when, on every cover, every matching family of its elements glues to exactly one
-- element at the covered object.
--
-- A cover of @a@ generates a sieve: every arrow into @a@ that factors through one of the cover's
-- legs. When the covers are stable and compose, the coverage generates a Grothendieck topology;
-- 'Sums' below shows that it need not. Covers are given by their legs here because that is what
-- someone writing a site down actually has -- a sieve is usually infinite, a list of legs is not.
-- Those sieves are also the truth values of a category of presheaves; see
-- "Proarrow.Profunctor.Instance.Sieve".
--
-- Asking for a sheaf rather than a bare profunctor rules out two specific failures. Say you want
-- @p a@ to be /data local to @a@/, and a cover of @a@ to be a way of taking that data apart. A
-- bare profunctor says nothing about how the whole relates to its parts, so it allows both of
-- these:
--
-- * /Too many wholes./ Two distinct elements at @a@ can restrict to the same family on the cover.
--   Then agreeing everywhere on a cover does not make two things equal, so nothing can be proved
--   by taking an object apart.
--
-- * /Too few./ A family on the cover that agrees on the overlaps can have no element at @a@
--   restricting to it. Then compatible local data cannot be assembled, so nothing can be built by
--   putting an object together.
--
-- The sheaf condition is exactly the absence of both -- see 'Sheaf' for the laws. Neither half
-- implies the other, and counting the two sides decides neither, as three presheaves from
-- @Props.Sheaf@ show:
--
-- @
--                                                elements at a   matching families   verdict
-- the representable at FLS, Atomic on BOOL             0                 1           too few
-- the constant presheaf, Joins on (BOOL, BOOL)         2                 1           too many
-- the collapsing presheaf, Atomic on BOOL              2                 2           not injective
-- @
--
-- Covers given by generating arrows, and gluing as an operation rather than a condition, follow
-- Arnaud Spiwack's /Sheaves in Haskell/ (Tweag, 2026, <https://www.tweag.io/blog/2026-06-18-sheaves-in-haskell/>).
-- What is added here is the category. Matching is stated as an equation over commuting squares: for
-- any @z@ and any @p :: z '~>' x@, @q :: z '~>' y@ with @'legArrow' g . p = 'legArrow' g' . q@,
-- @'lmap' p (m g) = 'lmap' q (m g')@. It quantifies over such @z@ rather than over /the/ pullback,
-- so the pullback of two legs need not exist as an object -- which is what lets 'Sums' work over a
-- free category that has none. Added too, in "Proarrow.Category.Enriched.Finitary.Sheaf": the
-- sieves, the classifier and a decision procedure for the sheaf condition.
module Proarrow.Category.Sheaf where

import Data.Kind (Constraint, Type)
import Data.List (subsequences, tails)
import Data.Maybe (fromMaybe, listToMaybe)
import Prelude (Bool, Maybe (..), and, error, not, null, (||))

import Proarrow.Category.Enriched.Finitary (Finitary (..), FiniteCat, LocallyFinite, factorThrough, foreachOb)
import Proarrow.Category.Enriched.Thin (Thin)
import Proarrow.Category.Instance.Collage (COLLAGE (..), Collage (..))
import Proarrow.Category.Instance.Free (Elem, FREE)
import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Category.Monoidal.Cartesian (Bicartesian)
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..), type (+))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (CAT, CategoryOf (..), Hom, Kind, Profunctor (..), Promonad (..), obj, rmap, (//), type (+->))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Limit.Pullback (HasPullbacks (..))
import Proarrow.Profunctor.Instance.Product (fstP, sndP, (:*:) (..))
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor (..))
import Proarrow.Profunctor.Instance.Yoneda (Yo (..))

-- * Sites

-- | A coverage, named @t@, on the category @k@. Several coverages can live on one category, so the
-- name is a parameter rather than a wrapper on the kind.
--
-- A cover is given by its /legs/, the generating arrows of the covering family. The identity cover,
-- which every coverage has, is left implicit: 'Cover' and 'covers' list the others. The laws are
--
-- [Stability] covers pull back. Given a cover @c@ of @a@ and any @f :: b '~>' a@, the object @b@
--   has a cover -- possibly just its identity -- each of whose legs @h@ satisfies
--   @f . h = 'legArrow' g . h'@ for some leg @g@ of @c@ and some @h'@. Only the equation is asked
--   for; no pullback object has to exist.
--
-- [Naming] a family over a cover is consulted only at that cover's legs. A family over @c@ is a
--   function @forall x. 'Leg' t k a c x -> r@, as 'glue' takes and 'PulledBack' carries, and
--   the legs of @c@ are those in @'legs' c@, or built from the cover's own data. Its values at any
--   other leg are unspecified, as 'glue'\'s value is on a family that does not match.
--
-- Naming is what the mathematics gets from dependent types. There a covering family is indexed
-- by its own index set, and a matching family is a dependent product over it: the type of a leg
-- depends on the cover /value/. Here it depends on the cover's type-level name instead, which is
-- faithful when the name is a singleton -- one cover per name, as for most coverages below. Where
-- covers share a name, as 'Atomic'\'s do on a category that is not thin and 'Joins'\'s always do,
-- the type also admits the legs of every other cover with that name, and the law is what says that
-- those are not asked about. A hand-written 'glue' therefore takes its legs from the cover it was
-- given.
type Site :: Type -> Kind -> Constraint
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
type SomeLeg :: Type -> forall (k :: Kind) -> k -> Type -> Type
data SomeLeg t k a c where
  SomeLeg :: Leg t k a c x -> SomeLeg t k a c

-- | A site whose covers can be listed, object by object. This is what the law tests and the
-- decision procedure of "Proarrow.Category.Enriched.Finitary.Sheaf" quantify over. A free category
-- is a 'Site' but not this: whether an object is a sum is not something its 'Ob' can answer.
--
-- Beyond 'Site'\'s Stability, listing the covers comes with a second law:
--
-- [Composition] covers compose. If @c@ covers @a@ and every leg of @c@ is itself covered, the
--   composites cover @a@ too. Stability and composition together are what make the coverage
--   generate a Grothendieck topology, and so make
--   'Proarrow.Category.Enriched.Finitary.Sheaf.closure' idempotent and meet-preserving --
--   without which the dense sieves at an object are not closed under meets, which is what
--   'Proarrow.Category.Enriched.Finitary.Sheaf.Plus' rests on.
--   'Proarrow.Testing.Laws.testLawvereTierney' is the check.
class (Site t k) => HasFiniteCovers t k where
  -- | The covers of an object, beyond the identity.
  covers :: forall (a :: k). (Ob a) => [SomeCover t k a]

-- | A cover of @a@, with its name hidden.
type SomeCover :: Type -> forall (k :: Kind) -> k -> Type
data SomeCover t k a where
  SomeCover :: Cover t k a c -> SomeCover t k a

-- | How an arrow into @a@ factors through a cover of @a@: the leg it goes through, and the arrow
-- to that leg\'s source. The equation @f = 'legArrow' g . h@ is the caller\'s to rely on and the
-- instance\'s to respect.
type Factors :: Type -> forall (k :: Kind) -> k -> Type -> k -> Type
data Factors t k a c x where
  Factors :: Leg t k a c y -> x ~> y -> Factors t k a c x

-- | How an arrow into @a@ factors through a cover of @a@, if it does: through the first leg it
-- factors through, found by 'factorThrough'. Only the hom-sets have to be finite.
factorThroughCover :: (Site t k, LocallyFinite k) => Cover t k a c -> x ~> a -> Maybe (Factors t k a c x)
factorThroughCover c h = listToMaybe [Factors l u | SomeLeg l <- legs c, Just u <- [h // legArrow l // factorThrough h (legArrow l)]]

-- | A cover pulled back along an arrow @f :: b '~>' a@: either @f@ itself factors through a leg --
-- the pullback is @b@\'s implicit identity cover -- or some cover of @b@ has every leg factoring
-- through one.
type PulledBack :: Type -> forall (k :: Kind) -> k -> Type -> k -> Type
data PulledBack t k a c b where
  AlreadyFactors :: Factors t k a c b -> PulledBack t k a c b
  PulledBack :: Cover t k b c' -> (forall x. Leg t k b c' x -> Factors t k a c x) -> PulledBack t k a c b

-- | 'Site'\'s Stability law as an /operation/: not merely that covers pull back, but a pullback
-- one can compute with, carrying the factorisation of each new leg through an old one.
--
-- This is what lets a sheaf be glued structurally rather than found. Without it, gluing into a
-- carrier that has no 'glue' of its own -- an internal hom, the closed sieves -- means searching
-- the carrier\'s elements for the one that restricts correctly
-- ('Proarrow.Category.Enriched.Finitary.Topos.glueBySearch'), which needs the carrier to be
-- finitary for a fact that has nothing to do with finiteness.
--
-- Separate from 'Site' because 'Sums' cannot implement it: a free bicartesian category is not
-- extensive, so its covers do not pull back at all -- see 'Sums'. That a coverage /is/ stable is
-- therefore visible in the instance list rather than in a paragraph.
class (Site t k) => StableSite t k where
  pullbackCover :: (Ob b) => Cover t k a c -> b ~> a -> PulledBack t k a c b

-- | A cover pulled back along the identity of the object it covers: itself, each leg factoring
-- through itself. Every instance needs this clause and none of them can get it wrong, which the
-- hand-written version cannot say -- there, naming another leg with the same source type-checks.
pullbackAlongId :: (Site t k) => Cover t k a c -> PulledBack t k a c a
pullbackAlongId c = PulledBack c \l -> legArrow l // Factors l id

-- * Sheaves

-- | A profunctor that is a sheaf for the coverage @t@ on the contravariant side: elements over a
-- cover glue. A family @m@ over the legs of a cover @c@ is /matching/ when it agrees on
-- overlaps: for legs @g@ and @g'@ and any @p :: z '~>' x@, @q :: z '~>' y@ with
-- @'legArrow' g . p = 'legArrow' g' . q@, @'lmap' p (m g) = 'lmap' q (m g')@. 'Sums' below is the
-- smallest worked instance of that condition, where it comes to one equation. The laws are
--
-- [Restriction] for matching @m@, @'lmap' ('legArrow' g) ('glue' c m) = m g@ at every leg @g@ of
--   @c@: the gluing restricts back to the family;
--
-- [Uniqueness] @'glue' c (\\g -> 'lmap' ('legArrow' g) x) = x@: an element is the gluing of its
--   own restrictions.
--
-- The laws constrain 'glue' on /matching/ families only, and its type accepts any family, so its
-- value on a non-matching one is unspecified. The 'Sums' instance below is the live example: it
-- keeps one leg's covariant component and discards the other, which is sound only because matching
-- forces them equal.
--
-- Together they say that restriction is a bijection from the elements at @a@ to the matching
-- families on @c@, which is the sheaf condition. Gluing is stated for every @b@ at once: a
-- profunctor @j '+->' k@ is a sheaf when, for each object @b@ of @j@, the presheaf @p (-) b@ on @k@
-- is one. Once the glued element at @(a, b)@ is fixed, 'dimap' fixes its value at every other point
-- @(g, h)@ of the sieve the cover generates -- which is why
-- "Proarrow.Category.Enriched.Finitary.Sheaf" can decide the same condition as natural
-- transformations out of that sieve.
--
-- Gluing is contravariant, and not by choice: a coverage presents each object by the arrows /into/
-- it, and @k@ is the side of @p a b@ that 'lmap' acts on. The dual needs a
-- /cocoverage/, which is a coverage on @'OPPOSITE' k@, and a cosheaf for it is
-- @'Sheaf' t ('Proarrow.Category.Instance.Opposite.Op' p)@; nothing supplies a cocoverage yet,
-- though @'Proarrow.Category.Enriched.Finitary.Finitary' ('Proarrow.Category.Instance.Opposite.Op' p)@
-- makes the machinery available for one.
-- The instances are indexed by the /shape/ of the profunctor: the limits just below, a site's
-- representables, and the image of sheafification
-- ('Proarrow.Category.Enriched.Finitary.Sheaf.Plus' twice over). One indexed by the /coverage/
-- instead cuts across that axis and so overlaps all of them -- which is why 'glueTrivial' is a
-- function and not an @instance 'Sheaf' 'Trivial' p@.
type Sheaf :: forall {j} {k}. Type -> j +-> k -> Constraint
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
-- instances above overlap -- at @'Sheaf' 'Trivial' 'TerminalProfunctor'@, say -- with neither more
-- specific than the other, so GHC could not choose between them. Write @glue = glueTrivial@ to get
-- the instance for one profunctor.
glueTrivial :: Cover Trivial k a c -> (forall x. Leg Trivial k a c x -> p x b) -> p a b
glueTrivial c _ = case c of {}

-- | The atomic coverage: every arrow into an object covers it, on its own. A composite of
-- singleton covers is a singleton cover, so listing every arrow is what makes the covers compose
-- -- and this is the first coverage here at which a leg of a cover is itself covered, so the first
-- at which 'HasFiniteCovers'\'s Composition law says anything at all. Stability is the pullback
-- square, which is why the instance asks for 'HasPullbacks': the pullback of the covering arrow
-- along the arrow it is pulled back along is the new cover, and the other projection factors the
-- new leg through the old one.
--
-- The sieve a single arrow generates is the arrows factoring through it, so a sieve here is dense
-- exactly when it is inhabited: this is the /atomic/ topology, of which 'HasPullbacks' is the Ore
-- condition. A sheaf is a profunctor whose restriction along every arrow is a bijection -- on a
-- chain, a presheaf that is constant up to iso, since every arrow of it is a cover.
--
-- The identity arrow is listed as a cover too. 'Site' leaves the identity cover implicit and
-- 'Proarrow.Category.Enriched.Finitary.Sheaf.isCovering' tests for the maximal sieve separately,
-- so the extra entry decides nothing that was not already decided; dropping it would take deciding
-- @b ~ a@ under 'foreachOb', which is not something a coverage generic in @k@ can do.
type data Atomic

-- | The name of the 'Atomic' cover of an object by a single arrow out of @b@: the 'Cover'
-- constructor is @Solely@ and its one 'Leg' constructor is @Only@. Two distinct arrows @b '~>' a@
-- share the name, so the name is not a singleton, and 'Site'\'s Naming law is what makes that
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

-- | The open-cover coverage of a finite distributive lattice: an object is covered by any family
-- of objects below it whose join it is. Read the lattice as the opens of a finite space and this is the site
-- whose sheaves are the sheaves on that space: a section over an open is determined by, and
-- assembled from, its sections over any opens that cover it. On the lattice of opens of the
-- discrete two-point space, @(BOOL, BOOL)@ (see "Proarrow.Category.Instance.Product"), the whole
-- space is covered by its two singletons and the empty set by no opens at all.
--
-- The empty family is a cover too, of the bottom element, since the bottom is its join. That
-- cover asks a sheaf for exactly one section over the bottom, which is what makes an empty open
-- behave like the empty set. On a chain nothing else is covered, since no element but the bottom
-- is a join of the ones strictly below it.
--
-- Covers are listed as the antichains strictly below an object that join to it, found by
-- enumerating subsets: exponential in the number of objects, so for small posets. Families that
-- are not antichains, or that contain the object itself, generate the same sieves as the listed
-- ones and so decide nothing new.
--
-- A distributive lattice is a thin 'Proarrow.Category.Monoidal.Cartesian.Bicartesian' category,
-- which is what the instances ask for: the meet is the product, the join the coproduct, and
-- 'Proarrow.Category.Monoidal.Distributive.Distributive' the law between them, checked by
-- 'Proarrow.Testing.Laws.testDistributive'. Distributivity is exactly stability: pulled back along
-- @b '<=' a@, a cover @{x_i}@ of @a@ becomes @{b '&&' x_i}@, whose join is @b '&&' a@ -- that
-- is, @b@ -- by distributivity and by nothing else. The covers compose, since a join of joins is a
-- join, so this is a Grothendieck topology, and it is subcanonical, since joins are colimits.
--
-- Subcanonical is about the representable /presheaves/. A two-sided @'Yo' a ('OP' b)@ need not be
-- a sheaf: the empty cover asks for exactly one element at the bottom for every object of @j@,
-- while @'Yo' a ('OP' b)@ has none at an object @b@ has no arrow to.
--
-- The instances ask for 'Thin' as well as 'Proarrow.Category.Monoidal.Cartesian.Bicartesian':
-- covers are found by asking whether there is an arrow at all, which reads as @<=@ only when there
-- is at most one. 'Proarrow.Category.Instance.FinSet.FINSET' is bicartesian and distributive too,
-- and this coverage would mean nothing there.
--
-- The finite, stable counterpart of 'Sums': both cover an object by its summands, and a
-- distributive lattice is the thin case of the extensivity that a free bicartesian category lacks.
type data Joins

-- | The name of every 'Joins' cover: the 'Cover' constructor is @ByJoin@, holding its legs, and
-- the 'Leg' constructor is @Under@, one per member of the family. A @ByJoin@ is a cover of @a@
-- only when its legs join to @a@; 'covers' lists exactly the antichains that do. All the covers
-- of an object share the name, so 'Site'\'s Naming law is doing real work here: a family over
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
-- injections. This is the syntactic site of Spiwack's post (see the module header) -- the free
-- bicartesian closed category 'Proarrow.Tools.CCC.Syntax' is one such category, with the booleans
-- the sum @TermF '+' TermF@ covered by @true@ and @false@.
--
-- Read @p a@ as the ways of producing a result of type @a@, and the module header's two failures
-- become concrete: too many is two elements of @p Bool@ with the same branches, so a proof by
-- cases establishes nothing; too few is a pair of branches with no conditional, so @if-then-else@
-- is not definable.
--
-- One caveat, and a real one: 'Site'\'s Stability law does /not/ hold for this coverage as
-- declared. Covers live only at objects whose shape is syntactically @x '+' y@, so stability would
-- need every arrow into a sum to decompose its domain -- that is /extensivity/, and a free
-- bicartesian category is not extensive. Two witnesses: @id '|||' 'lft'@ at
-- @(u '+' u) '+' u ~> u '+' u@ needs only coproducts, and its restriction to the left summand is
-- @id@, which factors through neither injection; and with a richer constraint list
-- @'Proarrow.Monoid.mempty' :: UnitF ~> u '+' u@ has a source that is not a sum at all, so no
-- cover is even available. Nothing here breaks -- 'glue'\'s laws below are the coproduct's
-- universal property and need no stability, and @FREE@ is deliberately not a 'HasFiniteCovers', so the
-- topology machinery is never instantiated at it -- but this coverage does not generate a
-- Grothendieck topology, and the licence that 'HasFiniteCovers'\'s 'covers' gives -- to check only
-- the covers it lists -- does not extend to it.
--
-- Being a sheaf is exactly @p Bool ≅ p TermF × p TermF@: every pair of branches has a
-- conditional, and only one. On a representable that conditional is @'|||'@, which is why 'glue'
-- below is @[t, e]@; the conditional on a /test/ @f :: c '~>' Bool@ with branches over @c@ is
-- 'Proarrow.Tools.CCC.either', which needs the distributive law as well.
--
-- The free category cannot list the covers of an arbitrary object, so this is a 'Site' and not a
-- 'HasFiniteCovers'.
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
-- The initial object is needed, even though the coproduct alone builds the gluing. An element of
-- @'Yo' x ('OP' b)@ at @z@ carries a second, covariant component @b '~>' d@, and a family over the
-- two injections carries one of those per leg, while the glued element can carry only one.
-- What forces the two to agree is the matching condition, and the two injections overlap only at
-- the initial object: @'lft' . initiate = 'rgt' . initiate@, so a matching family must take
-- equal values there, and the first components being initiate either way leaves exactly the
-- agreement of the second. Without an initial object the injections have no overlap at all, every
-- family is vacuously matching, and restriction fails for any @j@ with a hom-set bigger than one.
--
-- The decision procedure in "Proarrow.Category.Enriched.Finitary.Sheaf" does not need this,
-- because it reads the condition off the generated /sieve/, which carries every arrow of @j@ and
-- so ties the covariant components together on its own.
instance
  (HasBinaryCoproducts `Elem` cs, HasInitialObject `Elem` cs, CategoryOf j)
  => Sheaf Sums (Yo (x :: FREE cs (p :: CAT k)) (OP (b :: j)) :: j +-> FREE cs p)
  where
  glue BySummands m = case (m AtLeft, m AtRight) of
    (Yo f h, Yo g _) -> Yo (f ||| g) h

-- | __Any profunctor as a site.__ In the collage of @p@, an object @'R' b@ of the right layer is
-- covered by every arrow into it from the left -- that is, by the elements of @p@ at @b@, which
-- are exactly the cross-arrows. The left layer is covered by nothing.
--
-- The coverages above are put on a category they are given; this one builds its category, from
-- any finitary profunctor. That makes it the dependable source of sites that are /not posets/,
-- since @p@ may have several elements between one pair of objects and those are parallel legs. Two
-- familiar sites are instances: the walking arrow 'Proarrow.Category.Instance.Bool.BOOL' is the
-- collage of the one-element profunctor on the unit category, covered here as 'Atomic' covers it,
-- and the graph schema of @Examples.Graph@ is the collage of the two-element one, whose @ByEnds@
-- is this coverage under other names.
--
-- Stable and composing, and neither is a fact about a particular @p@. An arrow into @'R' b@ is
-- either a cross-arrow, which is itself a leg, or an @'InR' g@, along which the cover pulls back
-- to the cover of the source leg by leg -- because @'InR' g '.' 'L2R' x = 'L2R' ('rmap' g x)@,
-- which is a clause of the collage's own composition. The legs are left-layer objects and nothing
-- covers those, so composition is trivial.
--
-- A sheaf for it is a profunctor with descent data: its value at @'R' b@ is the matching families
-- over the elements of @p@, glued.
type data ByElements

-- | The name of 'ByElements'\'s cover of an object of the right layer, whose 'Cover' constructor
-- is @ByElements@ and whose 'Leg' constructor is @AtElement@, one leg per element of @p@.
type data Elements

instance (FiniteCat j, Finitary p) => Site ByElements (COLLAGE (p :: k +-> j)) where
  data Cover ByElements (COLLAGE p) a c where
    ByElements :: (Ob b) => Cover ByElements (COLLAGE p) (R b) Elements
  data Leg ByElements (COLLAGE p) a c x where
    AtElement :: (Ob a) => p a b -> Leg ByElements (COLLAGE p) (R b) Elements (L a)
  legArrow (AtElement x) = L2R x
  legs (ByElements @b) = foreachOb @j \ @a -> [SomeLeg (AtElement x) | x <- elements @p @a @b]

instance (FiniteCat j, Finitary p, CategoryOf k) => HasFiniteCovers ByElements (COLLAGE (p :: k +-> j)) where
  covers @a = case obj @a of
    InL _ -> []
    InR g -> [SomeCover ByElements] \\ g

instance (FiniteCat j, Finitary p, CategoryOf k) => StableSite ByElements (COLLAGE (p :: k +-> j)) where
  pullbackCover ByElements (L2R x) = x // AlreadyFactors (Factors (AtElement x) id)
  pullbackCover ByElements (InR g) = g // PulledBack ByElements \(AtElement y) -> Factors (AtElement (rmap g y)) id
