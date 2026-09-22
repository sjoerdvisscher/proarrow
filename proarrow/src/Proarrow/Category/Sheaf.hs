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
--                                        elements at a   matching families   verdict
-- the representable at FLS, ByArrow            0                 1           too few
-- the constant presheaf, Canonical             2                 1           too many
-- the collapsing presheaf, ByArrow             2                 2           not injective
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

import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..), IsBool (..))
import Proarrow.Category.Instance.Free (Elem, FREE)
import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..), type (+))
import Proarrow.Colimit.Initial (HasInitialObject)
import Proarrow.Core (CAT, CategoryOf (..), Kind, Profunctor (..), obj, type (+->))
import Proarrow.Profunctor.Instance.Product (fstP, sndP, (:*:) (..))
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor (..))
import Proarrow.Profunctor.Instance.Yoneda (Yo (..))

-- * Sites

-- | A coverage, named @t@, on the category @k@. Several coverages can live on one category, so the
-- name is a parameter rather than a wrapper on the kind.
--
-- A cover is given by its /legs/, the generating arrows of the covering family. The identity cover,
-- which every coverage has, is left implicit: 'Cover' and 'covers' list the others. The one law is
--
-- [Stability] covers pull back. Given a cover @c@ of @a@ and any @f :: b '~>' a@, the object @b@
--   has a cover -- possibly just its identity -- each of whose legs @h@ satisfies
--   @f . h = 'legArrow' g . h'@ for some leg @g@ of @c@ and some @h'@. Only the equation is asked
--   for; no pullback object has to exist.
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
class (Site t k) => HasFiniteCovers t k where
  -- | The covers of an object, beyond the identity.
  covers :: forall (a :: k). (Ob a) => [SomeCover t k a]

-- | A cover of @a@, with its name hidden.
type SomeCover :: Type -> forall (k :: Kind) -> k -> Type
data SomeCover t k a where
  SomeCover :: Cover t k a c -> SomeCover t k a

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

-- * Example sites

-- | The trivial coverage: only identities cover, so every profunctor is a sheaf.
type data Trivial

instance (CategoryOf k) => Site Trivial k where
  data Cover Trivial k a c
  data Leg Trivial k a c x
  legArrow g = case g of {}
  legs c = case c of {}

instance (CategoryOf k) => HasFiniteCovers Trivial k where
  covers = []

-- | Every profunctor is a sheaf for 'Trivial', by the eliminator of an empty 'Cover'. This is a
-- function rather than an @instance 'Sheaf' 'Trivial' p@ because that head and the two closure
-- instances above overlap -- at @'Sheaf' 'Trivial' 'TerminalProfunctor'@, say -- with neither more
-- specific than the other, so GHC could not choose between them. Write @glue = glueTrivial@ to get
-- the instance for one profunctor.
glueTrivial :: Cover Trivial k a c -> (forall x. Leg Trivial k a c x -> p x b) -> p a b
glueTrivial c _ = case c of {}

-- | The walking arrow 'BOOL' with 'TRU' covered by 'FLS' alone. The one leg has no overlap
-- with itself beyond its source, so every element at 'FLS' is a matching family, and a presheaf is
-- a sheaf exactly when its restriction along 'F2T' is a bijection. The coverage is stable, since
-- pulling the cover back along 'F2T' gives the identity of 'FLS', but not subcanonical: the
-- representable at 'FLS' has an element at 'FLS' and none at 'TRU', so it is not a sheaf.
type data ByArrow

-- | The name of 'ByArrow'\'s one cover, whose 'Cover' constructor is @TruByFls@ and whose one
-- 'Leg' constructor is @ViaF2T@.
type data TruByFls

instance Site ByArrow BOOL where
  data Cover ByArrow BOOL a c where
    TruByFls :: Cover ByArrow BOOL TRU TruByFls
  data Leg ByArrow BOOL a c x where
    ViaF2T :: Leg ByArrow BOOL TRU TruByFls FLS
  legArrow ViaF2T = F2T
  legs TruByFls = [SomeLeg ViaF2T]

instance HasFiniteCovers ByArrow BOOL where
  covers @a = case boolId @a of
    Fls -> []
    Tru -> [SomeCover TruByFls]

-- | The open-cover coverage of the discrete two-point space, whose opens are @(BOOL, BOOL)@ (see
-- "Proarrow.Category.Instance.Product"): the whole space is covered by its two singletons, and the
-- empty set by no opens at all. The covers are stable and compose, so the covering sieves are
-- exactly those whose union is the object; and since a union of opens is their colimit -- the
-- empty union included -- every representable presheaf is a sheaf: the coverage is subcanonical.
-- A sheaf has exactly one section over the empty set, and its sections over the whole space are
-- the pairs of sections over the two points.
--
-- Subcanonical is about the representable /presheaves/. A two-sided @'Yo' a ('OP' b)@ need not be
-- a sheaf: the empty cover asks for exactly one element at @'(FLS, FLS)@ for every object of @j@,
-- while @'Yo' a ('OP' b)@ has none at an object @b@ has no arrow to.
type data Canonical

-- | The name of 'Canonical'\'s cover of the whole space, whose 'Cover' constructor is @ByPoints@
-- and whose 'Leg' constructors are @AtX@ and @AtY@, one per singleton.
type data ByPoints

-- | The name of 'Canonical'\'s cover of the empty set, whose 'Cover' constructor is @ByNothing@
-- and which has no legs.
type data ByNothing

instance Site Canonical (BOOL, BOOL) where
  data Cover Canonical (BOOL, BOOL) a c where
    ByPoints :: Cover Canonical (BOOL, BOOL) '(TRU, TRU) ByPoints
    ByNothing :: Cover Canonical (BOOL, BOOL) '(FLS, FLS) ByNothing
  data Leg Canonical (BOOL, BOOL) a c x where
    AtX :: Leg Canonical (BOOL, BOOL) '(TRU, TRU) ByPoints '(TRU, FLS)
    AtY :: Leg Canonical (BOOL, BOOL) '(TRU, TRU) ByPoints '(FLS, TRU)
  legArrow AtX = Tru :**: F2T
  legArrow AtY = F2T :**: Tru
  legs ByPoints = [SomeLeg AtX, SomeLeg AtY]
  legs ByNothing = []

instance HasFiniteCovers Canonical (BOOL, BOOL) where
  covers @a = case obj @a of
    Tru :**: Tru -> [SomeCover ByPoints]
    Fls :**: Fls -> [SomeCover ByNothing]
    _ -> []

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
