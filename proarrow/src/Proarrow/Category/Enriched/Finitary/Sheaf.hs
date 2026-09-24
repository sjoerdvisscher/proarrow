{-# LANGUAGE AllowAmbiguousTypes #-}
-- The instances on 'SHEAVES' are orphans for the reason "Proarrow.Category.Enriched.Finitary.Topos"
-- gives for its own: the kind is 'SUBCAT' of a predicate, and both come from other modules.
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Sheaves on a finite site, decided by enumeration.
--
-- A cover of @a@ generates a 'Sieve' ('generatedSieve'), and a matching family for that cover is
-- exactly a natural transformation out of the sieve -- which over finitary profunctors is a finite
-- thing you can list. So the sheaf condition becomes a comparison of two finite lists ('sheafAt'):
-- restrict each element at @a@ to get one table per element, enumerate the matching families to get
-- the other list, and check the two agree as multisets. Comparing only their /lengths/ is not
-- enough: @Props.Sheaf@'s @Collapse@ has as many elements as matching families and is still not a
-- sheaf.
--
-- The same coverage is a Lawvere–Tierney topology on the topos. 'closure' sends a sieve to the pairs
-- @(g, h)@ along which it pulls back to a covering one, and 'lawvereTierney' packages that as an
-- arrow on 'Omega'.
--
-- The topology also has a /sheafification/, 'Sheafify', with its unit and universal property --
-- computed rather than postulated, so it is one more thing that can be enumerated and compared.
module Proarrow.Category.Enriched.Finitary.Sheaf where

import Data.Kind (Type)
import Data.List (find, genericIndex, genericLength, sort)
import Data.Map.Strict qualified as M
import Data.Maybe (fromMaybe, isJust, listToMaybe, mapMaybe)
import Numeric.Natural (Natural)
import Prelude (type (~))
import Prelude qualified as P

import Proarrow.Category.Enriched.Finitary
  ( Finitary (..)
  , FiniteCat
  , LocallyFinite
  , factorThrough
  , factorsThrough
  , foreachOb
  )
import Proarrow.Category.Enriched.Finitary.Topos
  ( FINITARY
  , KnownTables
  , Reindex
  , Retabulation (..)
  , Tabulated
  , coequalizeNat
  , equalizeNat
  , factorThroughEqualizer
  , familyIndex
  , fromTabulated
  , graphSieve
  , natDomain
  , natElements
  , natIndex
  , natKey
  , natPositionsBy
  , natTable
  , preimageMaybe
  , sieveTable
  , toTabulated
  , withSubobject
  , withTables
  )
import Proarrow.Category.Enriched.Thin (Enumerable)
import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Sheaf
  ( Factors (..)
  , HasFiniteCovers (..)
  , PulledBack (..)
  , Sheaf (..)
  , Site (..)
  , SomeCover (..)
  , SomeLeg (..)
  , StableSite (..)
  )
import Proarrow.Category.Topos (ElementaryTopos, HasEpiMonoFactorization, HasSubobjectClassifier (..))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.Coequalizer (HasCoequalizers (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Colimit.Pushout (HasPushouts (..))
import Proarrow.Core
  ( CategoryOf (..)
  , OB
  , Profunctor (..)
  , Promonad (..)
  , UN
  , (//)
  , (\\)
  , type (+->)
  , type (:&&:)
  , type (:~>)
  )
import Proarrow.Limit.BinaryProduct (PROD (..), Prod (..))
import Proarrow.Limit.Equalizer (HasEqualizers (..))
import Proarrow.Limit.Pullback (HasPullbacks)
import Proarrow.Profunctor.Instance.Coproduct ((:+:) (..))
import Proarrow.Profunctor.Instance.Exponential ((:~>:) (..))
import Proarrow.Profunctor.Instance.Initial (InitialProfunctor)
import Proarrow.Profunctor.Instance.Product ((:*:) (..))
import Proarrow.Profunctor.Instance.Sieve (Sieve (..), maximalSieve, sieveMeet)
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor (..))
import Proarrow.Profunctor.Instance.Yoneda (Yo (..))

-- * Sieves and their closure

-- | The sieve a cover generates at @(a, b)@: the arrows into @a@ that factor through a leg,
-- paired with every arrow out of @b@.
generatedSieve
  :: forall t {j} {k} (a :: k) (b :: j) c
   . (Site t k, LocallyFinite k, CategoryOf j, Ob a, Ob b)
  => Cover t k a c
  -> Sieve a b
generatedSieve c = Sieve \g _ -> P.any (\(SomeLeg l) -> let f = legArrow l in factorsThrough g f \\ f \\ g) (legs c)

-- | Whether a sieve is the maximal one -- every arrow of the category is in it.
isMaximal :: forall {j} {k} (a :: k) (b :: j). (FiniteCat j, FiniteCat k) => Sieve a b -> P.Bool
isMaximal s = P.and (sieveTable s)

-- | Whether every point of the second sieve is a point of the first.
contains :: forall {j} {k} (a :: k) (b :: j). (FiniteCat j, FiniteCat k) => Sieve a b -> Sieve a b -> P.Bool
contains s = \s' -> P.and (P.zipWith (\x y -> P.not y P.|| x) ts (sieveTable s'))
  where
    -- tabulated before the second sieve arrives, so a partial application tabulates @s@ once
    ts = sieveTable s

-- | Whether a sieve is covering: either it is the maximal sieve, or it contains the sieve that some
-- cover of its object generates -- which, a sieve being closed under composition, is to contain
-- that cover's legs ('coveringCover').
--
-- That is the coverage taken at face value. It agrees with the Grothendieck topology the coverage
-- generates only when the covers are stable and compose. When they do not, 'closure' stops being
-- idempotent, and 'Proarrow.Testing.Laws.testLawvereTierney' is where that shows up.
isCovering
  :: forall t {j} {k} (a :: k) (b :: j)
   . (HasFiniteCovers t k, FiniteCat j, FiniteCat k)
  => Sieve a b
  -> P.Bool
isCovering s = isMaximal s P.|| isJust (coveringCover @t s)

-- | The first listed cover all of whose legs lie in the sieve, if there is one. This is the search
-- 'isCovering' makes and the one 'extendPlus' needs, and it needs no tabulation: whether a sieve
-- contains the legs at the identity decides whether it contains everything they generate.
--
-- So it trusts the closure "Proarrow.Profunctor.Instance.Sieve" does not enforce: on a hand-built
-- predicate that is not a sieve it says yes where comparing the whole generated sieve says no.
coveringCover
  :: forall t {j} {k} (a :: k) (b :: j)
   . (HasFiniteCovers t k, CategoryOf j)
  => Sieve a b
  -> P.Maybe (SomeCover t k a)
coveringCover (Sieve s) = find (\(SomeCover c) -> P.all (\(SomeLeg l) -> s (legArrow l) id) (legs c)) (covers @t @k @a)

-- | The Lawvere–Tierney closure of a sieve: the pairs @(g, h)@ along which it pulls back to a
-- covering one. A sieve is covering exactly when its closure is the maximal sieve.
--
-- Note /both/ components -- @'dimap' g h@, not just @'lmap' g@. A coverage constrains only the
-- contravariant side, but a sieve over @j '+->' k@ has two, which is why @Props.Sheaf@ checks this
-- function's naturality at a non-trivial @j@.
closure
  :: forall t {j} {k} (a :: k) (b :: j)
   . (HasFiniteCovers t k, FiniteCat j, FiniteCat k)
  => Sieve a b
  -> Sieve a b
closure s@Sieve{} = Sieve \g h -> isCovering @t (dimap g h s) \\ g \\ h

-- | Whether a sieve is /closed/ for the topology: its own 'closure'. These are the truth values
-- of the sheaf topos, as the sieves are of the presheaf one -- see 'ClosedSieve'.
isClosed
  :: forall t {j} {k} (a :: k) (b :: j)
   . (HasFiniteCovers t k, FiniteCat j, FiniteCat k)
  => Sieve a b
  -> P.Bool
isClosed s = sieveTable (closure @t s) P.== sieveTable s

-- | The coverage as a Lawvere–Tierney topology on the topos of finitary profunctors: 'closure', as
-- an arrow on the subobject classifier.
lawvereTierney
  :: forall t j k. (HasFiniteCovers t k, FiniteCat j, FiniteCat k) => (Omega :: PROD (FINITARY j k)) ~> Omega
lawvereTierney = Prod (Sub (Prof \s@Sieve{} -> closure @t s))

-- * Deciding the sheaf condition

-- | Whether a finitary profunctor is a sheaf for the coverage: at every pair of objects and every
-- cover, restriction is a bijection from the elements at the covered object to the matching
-- families on the sieve the cover generates.
isSheaf
  :: forall t {j} {k} (p :: j +-> k)
   . (HasFiniteCovers t k, Finitary p, FiniteCat j, FiniteCat k)
  => P.Bool
isSheaf =
  P.and
    ( foreachOb @k \ @a ->
        let cs = covers @t @k @a -- does not depend on @b@, so bound outside the inner walk
        in foreachOb @j \ @b -> [sheafAt @t @p @a @b c | SomeCover c <- cs]
    )

-- | The sheaf condition at one cover: the restrictions of the elements at the covered object are
-- exactly the matching families on the sieve it generates, as multisets.
sheafAt
  :: forall t {j} {k} (p :: j +-> k) (a :: k) (b :: j) c
   . (Site t k, Finitary p, FiniteCat j, FiniteCat k, Ob a, Ob b)
  => Cover t k a c
  -> P.Bool
sheafAt c = withSieve (generatedSieve @t @a @b c) \ @q incl ->
  sort [natTable @q @p (\y -> case incl y of Yo g h -> dimap g h x) | x <- elements @p @a @b]
    P.== sort (natElements @q @p)

-- | A sieve as a subobject of the representable, handed on with its inclusion: the natural
-- transformations out of that subobject are exactly the matching families on the sieve, with no
-- separate treatment of the points outside it and no argument about which naturality conditions
-- may be dropped. This is the one notion of matching family in the module; 'sheafAt' and 'Plus'
-- both go through it.
--
-- 'withSubobject' checks the closure a sieve must have, and its failure branch is unreachable for
-- any coverage, lawful or not: 'generatedSieve'\'s membership ignores its covariant argument and
-- is closed under precomposition, and 'leastDenseSieve' is a meet of sieves. Reaching it would take
-- a 'Finitary' instance on the hom-profunctor whose 'elements' omits an arrow, which
-- 'Proarrow.Testing.Laws.testFinitary' rules out.
withSieve
  :: forall {j} {k} (a :: k) (b :: j) r
   . (FiniteCat j, FiniteCat k)
  => Sieve a b
  -> (forall q. (Finitary q) => (q :~> Yo a (OP b)) -> r)
  -> r
withSieve (Sieve s) k =
  withSubobject @(Yo a (OP b))
    (\(Yo g h) -> s g h)
    (\ @q (Sub (Prof incl)) -> k @q incl)
    (P.error "withSieve: not a sieve")

-- * Presenting a sheaf by its tables

-- | Present a finitary profunctor by its tables, as
-- 'Proarrow.Category.Enriched.Finitary.Topos.withTabulated' does, and tag the presentation with the
-- coverage -- which is to give it a 'Sheaf' instance. What that instance asserts is decided here,
-- by 'isSheaf', so the assertion is backed by an enumeration and not by the caller\'s word; the
-- failure continuation is taken when the profunctor is no sheaf for @t@.
--
-- This is how a sheaf with no 'Sheaf' instance of its own -- a representable, a sheafification --
-- becomes an object of 'SHEAVES'. It is also the cheap way to be one: the condition is decided on
-- the tables rather than on @p@, where a 'Sheafify' answers a single 'toIndex' by re-running the
-- whole plus construction.
withTabulatedSheaf
  :: forall t {j} {k} (p :: j +-> k) r
   . (HasFiniteCovers t k, Finitary p, FiniteCat j, FiniteCat k)
  => ( forall {lm} {rm} (tab :: j +-> k)
        . (tab ~ Tabulated t lm rm, KnownTables j k lm rm, Sheaf t tab)
       => (p :~> tab)
       -> (tab :~> p)
       -> r
     )
  -> r
  -> r
withTabulatedSheaf ok notSheaf = withTables @p \ @lm @rm ->
  if isSheaf @t @(Tabulated t lm rm :: j +-> k)
    then ok @(Tabulated t lm rm) toTabulated fromTabulated
    else notSheaf

-- | 'withTabulatedSheaf' where the profunctor is already a 'Sheaf': the tag is then justified by
-- the instance, so there is nothing to decide and no failure branch. This is what the colimits
-- below present their apex with -- it is a 'Sheafify', a sheaf by construction -- where the test
-- palettes, which have the fact but no instance, need the deciding one.
--
-- Presenting the apex matters rather more than it looks: it is handed to a continuation that will
-- ask it for its elements many times over, and an unpresented 'Sheafify' re-runs the whole plus
-- construction on each, one level for each colimit it is built from.
withSheafTables
  :: forall t {j} {k} (p :: j +-> k) r
   . (Sheaf t p, Finitary p, FiniteCat j, FiniteCat k)
  => ( forall {lm} {rm} (tab :: j +-> k)
        . (tab ~ Tabulated t lm rm, KnownTables j k lm rm, Sheaf t tab)
       => (p :~> tab)
       -> (tab :~> p)
       -> r
     )
  -> r
withSheafTables ok = withTables @p \ @lm @rm -> ok @(Tabulated t lm rm) toTabulated fromTabulated

-- * Descent

-- | Extend a /partial/ natural transformation into a sheaf to a total one, by gluing: where the
-- partial function is undefined at an element, it is defined on a cover of that element, and the
-- values there glue.
--
-- This is the plus construction\'s descent step with the carrier left open, so 'extendPlus' is
-- this at @'Plus' t p@, where the partial function is the value itself and the sieve below is its
-- 'support'. The colimits further down need the same step for a different reason: an epimorphism
-- of sheaves is only /locally/ surjective, so a projection having no preimage for an element is
-- the normal case there, not an error.
--
-- One level of descent: the cover is one of the listed ones, and its legs must be where the
-- partial function is already defined. The family glued there is matching whenever the partial
-- function is -- for the callers below, that is the hypothesis that the arrow being factored is
-- constant on the fibres it factors through -- so 'glue' is being used within its laws.
factorLocally
  :: forall t {j} {k} (p :: j +-> k) q
   . (HasFiniteCovers t k, CategoryOf j, Profunctor p, Sheaf t q)
  => (forall c d. (Ob c, Ob d) => p c d -> P.Maybe (q c d))
  -> p :~> q
factorLocally f y =
  y // case f y of
    P.Just v -> v
    P.Nothing -> case coveringCover @t (domainSieve y) of
      P.Just (SomeCover c) ->
        -- the error is unreachable: 'coveringCover' returned this cover by testing these same legs
        glue @t c \l -> fromMaybe (P.error "factorLocally: a leg outside the domain") (f (lmap (legArrow l) y) \\ legArrow l)
      P.Nothing -> P.error "factorLocally: the partial transformation is not defined on a cover of this element"
  where
    -- where the partial function is defined on restrictions of @y@; a sieve, since a restriction
    -- of a restriction is one. Taking the element as an argument is what pins its objects.
    domainSieve :: forall (a :: k) (b :: j). (Ob a, Ob b) => p a b -> Sieve a b
    domainSieve x = Sieve \g _ -> isJust (f (lmap g x)) \\ g

-- | Factor through a map that is onto only locally: @'factorLocally'@ of the preimage search.
-- Where 'Proarrow.Category.Enriched.Finitary.Topos.factorThroughCoequalizer' asks the map to be
-- onto, this asks only what being epi in the sheaves actually gives.
--
-- A pushout wants this for its /pair/ of injections, which are jointly locally onto rather than
-- separately: that is this at the coproduct, since two arrows into an object are one arrow out of
-- @a ':+:' b@ -- and one search over that is also one 'toIndex' of the element rather than two.
factorThroughLocalEpi
  :: forall t {j} {k} (c :: j +-> k) x c'
   . (HasFiniteCovers t k, CategoryOf j, Finitary c, Finitary x, Sheaf t c')
  => (x :~> c)
  -> (x :~> c')
  -> c :~> c'
factorThroughLocalEpi proj h = factorLocally @t \y -> P.fmap h (preimageMaybe proj y)

-- * Sheafification

-- | One step of the plus construction for the topology @t@. An element at @(a, b)@ is a matching
-- family on a dense sieve, taken up to agreement on a dense sieve; a 'Plus' value holds one such
-- family, as a partial function whose support is its sieve -- the sieve is never stored separately
-- and so cannot disagree with the family. On a finite site whose coverage is a Grothendieck topology
-- the dense sieves have a least one, 'leastDenseSieve', and every element has exactly one family on
-- it: so the element a value stands for is its restriction to that sieve, 'plusTable', and that is
-- what 'Finitary' numbers and "Proarrow.Testing" compares. Nothing has to be quotiented.
--
-- That is 'HasFiniteCovers'\'s Composition law, and 'leastDenseSieve' fails loudly rather than
-- compute where it does not hold.
--
-- __The constructor checks none of__: that the support is a sieve, that it is dense, that the
-- family is matching -- as 'Sieve'\'s does not check closure. 'plusElements' builds only lawful
-- values; one built by hand is its builder's responsibility.
type Plus :: forall {j} {k}. Type -> j +-> k -> j +-> k
data Plus t p a b where
  Plus :: (Ob a, Ob b) => (forall c d. c ~> a -> b ~> d -> P.Maybe (p c d)) -> Plus t p a b

instance (CategoryOf j, CategoryOf k) => Profunctor (Plus t p :: j +-> k) where
  dimap l r (Plus f) = l // r // Plus \g h -> f (l . g) (h . r)
  r \\ Plus{} = r

-- | The sieve a value is defined on.
support :: Plus t p :~> Sieve
support (Plus f) = Sieve \g h -> isJust (f g h)

-- | Whether a sieve is dense for the topology: its 'closure' is the maximal sieve. On a lawful
-- coverage this agrees with 'isCovering' -- 'Proarrow.Testing.Laws.testDenseIsCovering' checks
-- that -- but it is the stable notion, and 'Plus' needs stability, since 'dimap' pulls a support
-- back along arrows.
isDense
  :: forall t {j} {k} (a :: k) (b :: j)
   . (HasFiniteCovers t k, FiniteCat j, FiniteCat k)
  => Sieve a b
  -> P.Bool
isDense s = isMaximal (closure @t s)

-- | The meet of all the dense sieves at a pair of objects, and so the least dense sieve -- when
-- the covers compose, since that is what makes 'closure' preserve meets. Restriction to it is what
-- picks one matching family out of each element of 'Plus'. On a coverage whose covers pull back but
-- do not compose the meet need not be dense, and this errors, naming the law that failed, rather
-- than let 'Plus' compute on it: a poset @w ≤ x ≤ a@, @w ≤ y ≤ a@ with @a@ covered by @x@ and by
-- @y@ separately and each of those by @w@ is the smallest example.
leastDenseSieve
  :: forall t {j} {k} (a :: k) (b :: j)
   . (HasFiniteCovers t k, FiniteCat j, FiniteCat k, Ob a, Ob b)
  => Sieve a b
leastDenseSieve
  | isDense @t s = s
  | P.otherwise = P.error "leastDenseSieve: the dense sieves have no least one -- the covers do not compose"
  where
    s = P.foldr sieveMeet maximalSieve (P.filter (isDense @t) (elements @(Sieve :: j +-> k) @a @b))

-- | The elements of 'Plus' at a pair of objects: the matching families on the least dense sieve, in
-- the order 'natElements' lists them.
plusElements
  :: forall t {j} {k} (p :: j +-> k) (a :: k) (b :: j)
   . (HasFiniteCovers t k, Finitary p, FiniteCat j, FiniteCat k, Ob a, Ob b)
  => [Plus t p a b]
plusElements = withSieve (leastDenseSieve @t @a @b) \ @q incl ->
  -- the sieve's points as points of the representable, at the positions a row lists them
  let pos = natPositionsBy @q \y -> natKey (incl y)
  in [ Plus \g h -> g // h // P.fmap (fromIndex @p P.. (row P.!!)) (M.lookup (natKey (Yo g h)) pos)
     | row <- natElements @q @p
     ]

-- | A value restricted to a sieve reified as a subobject: the natural transformation out of it
-- that the value's family is.
restrictTo
  :: forall {j} {k} q (a :: k) (b :: j) t (p :: j +-> k)
   . (q :~> Yo a (OP b))
  -> Plus t p a b
  -> q :~> p
restrictTo incl (Plus f) y = case incl y of
  Yo g h ->
    fromMaybe (P.error "restrictTo: the sieve is not inside the support -- see HasFiniteCovers's Composition law") (f g h)

-- | A value's restriction to the least dense sieve, as its 'natTable': the indices of its values
-- at that sieve's points. See 'Plus' for what that determines.
plusTable
  :: forall t {j} {k} (p :: j +-> k) (a :: k) (b :: j)
   . (HasFiniteCovers t k, Finitary p, FiniteCat j, FiniteCat k)
  => Plus t p a b
  -> [Natural]
plusTable x@Plus{} = withSieve (leastDenseSieve @t @a @b) \ @q incl -> natTable @q @p (restrictTo incl x)

-- | Whether two values stand for the same element: their restrictions to the least dense sieve
-- agree. One sieve for the pair, where two 'plusTable's would each build their own -- which is what
-- "Proarrow.Testing"\'s equality on 'Plus' wants, since it compares far more often than it shows.
samePlus
  :: forall t {j} {k} (p :: j +-> k) (a :: k) (b :: j)
   . (HasFiniteCovers t k, Finitary p, FiniteCat j, FiniteCat k)
  => Plus t p a b
  -> Plus t p a b
  -> P.Bool
samePlus x@Plus{} y = withSieve (leastDenseSieve @t @a @b) \ @q incl ->
  -- one walk for the pair, and one 'toIndex' per point: at 'Sheafify' that is itself an enumeration
  P.and
    (natDomain @q @P.Bool \ @c @d z -> let ix = toIndex @p @c @d in ix (restrictTo incl x z) P.== ix (restrictTo incl y z))

-- | Numbered by 'plusElements', as the internal hom is numbered by the natural transformations
-- out of its weight.
instance (HasFiniteCovers t k, Finitary p, FiniteCat j, FiniteCat k) => Finitary (Plus t p :: j +-> k) where
  size @a @b = genericLength (plusElements @t @p @a @b)

  -- above the argument lambda: the sieve too, not just 'natIndex'\'s enumeration
  toIndex @a @b = withSieve (leastDenseSieve @t @a @b) \ @q incl ->
    let ix = natIndex @q @p "toIndex: not natural on the least dense sieve"
    in \x -> ix (restrictTo incl x)
  fromIndex @a @b = genericIndex (plusElements @t @p @a @b)
  elements @a @b = plusElements @t @p @a @b

-- | Sheafification: the plus construction twice. One 'Plus' makes a profunctor /separated/ -- two
-- elements with the same restrictions to a dense sieve are equal -- and the second makes it a
-- sheaf. The first alone need not: @Props.Sheaf@'s constant presheaf on the two-point space has one
-- section over the empty set after one plus, but still two over the whole space where a sheaf needs
-- four. On a site whose covers have no overlaps, 'Proarrow.Category.Sheaf.Atomic' on the walking
-- arrow say, one plus is
-- already a sheaf and the second changes nothing.
type Sheafify :: forall {j} {k}. Type -> j +-> k -> j +-> k
type Sheafify t p = Plus t (Plus t p)

-- | The unit of the plus construction: an element as the family of its own restrictions, on the
-- maximal sieve.
unitPlus :: forall t {j} {k} (p :: j +-> k). (Profunctor p) => p :~> Plus t p
unitPlus x = Plus (\g h -> P.Just (dimap g h x)) \\ x

-- | 'unitPlus' twice: the unit of sheafification.
unitSheafify :: forall t {j} {k} (p :: j +-> k). (Profunctor p) => p :~> Sheafify t p
unitSheafify x = unitPlus @t (unitPlus @t x)

-- | The universal property, one plus at a time: a map into a sheaf extends along 'unitPlus'. A
-- dense support either is everything, and the family is read off at the identity, or contains the
-- legs of some listed cover -- that is what density at the identity says, and 'coveringCover' finds
-- it -- and the family restricted to those legs glues. Which cover is found does not matter, @q@
-- being a sheaf; nor need @q@ be 'Finitary' -- gluing is all that is asked of it.
extendPlus
  :: forall t {j} {k} (p :: j +-> k) q
   . (HasFiniteCovers t k, Sheaf t q)
  => (p :~> q) -> Plus t p :~> q
extendPlus n = factorLocally @t \(Plus f) -> P.fmap n (f id id)

-- | Gluing for the plus construction: a matching family over a cover, assembled into one family.
-- At @(g, h)@ it takes the first leg that @g@ factors through and whose family is defined at the
-- factor -- 'factorThrough' gives that factor @u@, and the value is the leg's family at @(u, h)@.
-- So the support of the result is what the legs generate from the legs' own supports, which is
-- dense by 'Proarrow.Category.Sheaf.HasFiniteCovers'\'s Composition law.
--
-- Well definedness -- that another leg, or another factorisation through the same leg, gives the
-- same value -- is exactly what /matching/ says, and 'glue' is unconstrained on families that are
-- not matching, so the first one found is as good as any.
gluePlus
  :: forall t {j} {k} (q :: j +-> k) (a :: k) c (b :: j)
   . (Site t k, LocallyFinite k, Ob a, Ob b)
  => Cover t k a c
  -> (forall x. Leg t k a c x -> Plus t q x b)
  -> Plus t q a b
gluePlus c m =
  let ls = legs c
  in Plus \g h ->
       -- matching @Plus f@ is what brings the leg's source into scope, as 'plusTable' also relies on
       g // listToMaybe (mapMaybe (\(SomeLeg l) -> case m l of Plus f -> factorThrough g (legArrow l) P.>>= \u -> f u h) ls)

-- | Sheafification lands in the sheaves. This is the theorem @Props.Sheaf@ checks by enumeration
-- with @'isSheaf' \@t \@('Sheafify' t p)@; here it is as an instance, so a 'Sheafify' can be used
-- wherever a 'Sheaf' is asked for.
--
-- 'gluePlus' would type-check for any @'Plus' t q@, but its laws need @q@ /separated/ -- which
-- @'Plus' t p@ always is, so the head is the double plus. The single-plus statement that is also
-- true, @'Sheaf' t p => 'Sheaf' t ('Plus' t p)@, is thereby foreclosed for good: it would overlap
-- this one with neither more specific.
instance (Site t k, LocallyFinite k, CategoryOf j) => Sheaf t (Sheafify t (p :: j +-> k)) where
  glue = gluePlus @t

-- | 'extendPlus' twice: a map into a sheaf extends along 'unitSheafify'.
extendSheafify
  :: forall t {j} {k} (p :: j +-> k) q
   . (HasFiniteCovers t k, Sheaf t q)
  => (p :~> q) -> Sheafify t p :~> q
extendSheafify n = extendPlus @t (extendPlus @t n)

-- * The truth values of the topos

-- | A sieve that is its own 'closure'. The subobject classifier of the sheaves for @t@, as 'Sieve'
-- is of the presheaves: a subsheaf of @p@ is classified by sending an element to the sieve of
-- arrows carrying it into the subsheaf, and that sieve is closed exactly because the subsheaf
-- glues -- an element covered by ones that land in it lands in it.
--
-- As an object of @'FINITARY' j k@ this is the equalizer of 'lawvereTierney' and the identity on
-- 'Omega', which 'equalizeNat' would build and
-- 'Proarrow.Category.Enriched.Finitary.Topos.Reindex' would carry. It is a newtype instead
-- because 'Omega' is a /type family/: the object has to be nameable, and the table
-- 'withSubobject' carves along is bound existentially.
--
-- Being a classifier at all needs the coverage to be a Grothendieck topology -- 'closure'
-- idempotent and meet-preserving, which is 'HasFiniteCovers'\'s Composition law.
-- 'Proarrow.Testing.Laws.testLawvereTierney_' is where that is checked; where it fails this
-- computes something that is not the classifier, rather than failing as 'leastDenseSieve' does.
--
-- __The constructor checks nothing__, as 'Sieve'\'s and 'Plus'\'s do not; 'elements' below
-- produces only closed ones, and 'closedSieve' makes any sieve into one.
type ClosedSieve :: forall {j} {k}. Type -> j +-> k
newtype ClosedSieve t (a :: k) (b :: j) = ClosedSieve (Sieve a b)

-- | Closure commutes with 'dimap' -- that is the Lawvere–Tierney axiom 'lawvereTierney' packages
-- as an arrow on 'Omega' -- so a restriction of a closed sieve is closed.
instance (CategoryOf j, CategoryOf k) => Profunctor (ClosedSieve t :: j +-> k) where
  dimap l r (ClosedSieve s) = ClosedSieve (dimap l r s)
  x \\ ClosedSieve s = x \\ s

-- | The closed sieves at a pair of objects, in the order 'Sieve' lists them.
closedSieves
  :: forall t {j} {k} (a :: k) (b :: j)
   . (HasFiniteCovers t k, FiniteCat j, FiniteCat k, Ob a, Ob b)
  => [ClosedSieve t a b]
closedSieves = [ClosedSieve s | s <- elements @(Sieve :: j +-> k) @a @b, isClosed @t s]

instance (HasFiniteCovers t k, FiniteCat j, FiniteCat k) => Finitary (ClosedSieve t :: j +-> k) where
  size @a @b = genericLength (closedSieves @t @a @b)

  -- the closed ones are found by filtering every sieve, so that walk is bound outside the lambda
  toIndex @a @b =
    let tables = P.map (\(ClosedSieve s) -> sieveTable s) (closedSieves @t @a @b)
    in \(ClosedSieve s) -> familyIndex "toIndex: not a closed sieve" tables (sieveTable s)
  fromIndex @a @b = genericIndex (closedSieves @t @a @b)
  elements @a @b = closedSieves @t @a @b

-- | Whether an arrow pair is in a closed sieve.
inClosedSieve :: forall {j} {k} t (a :: k) (b :: j) c d. ClosedSieve t a b -> c ~> a -> b ~> d -> P.Bool
inClosedSieve (ClosedSieve (Sieve s)) g h = s g h

-- | The classifier is a sheaf, and like the internal hom it is built rather than found: the glued
-- sieve, asked about an arrow @g@, pulls the cover back along @g@ and asks each leg of the
-- pullback of the family member it factors through.
--
-- That reading is forced both ways, which is what makes it well defined. A sieve is closed under
-- precomposition, so an arrow in the glued sieve has every restriction of it in there too; and the
-- sieve is /closed/, so an arrow all of whose restrictions along a covering family are in it is in
-- it. Hence: in, exactly when every leg of the pullback is.
instance (StableSite t k, CategoryOf j) => Sheaf t (ClosedSieve t :: j +-> k) where
  glue c m =
    ClosedSieve
      ( Sieve \g h ->
          g // case pullbackCover c g of
            AlreadyFactors (Factors l u) -> inClosedSieve (m l) u h
            PulledBack c' factorsThroughLeg ->
              P.all (\(SomeLeg l') -> case factorsThroughLeg l' of Factors l u -> inClosedSieve (m l) u h) (legs c')
      )

-- | Any sieve as a closed one: 'lawvereTierney' corestricted to its fixed points, which is the
-- reflection of the presheaf classifier onto the sheaf one.
closedSieve
  :: forall t {j} {k} (a :: k) (b :: j)
   . (HasFiniteCovers t k, FiniteCat j, FiniteCat k)
  => Sieve a b
  -> ClosedSieve t a b
closedSieve s = ClosedSieve (closure @t s)

-- * The category of sheaves

-- | The full subcategory of @'FINITARY' j k@ on the sheaves for @t@: the finitary profunctors that
-- have a 'Sheaf' instance. Its finite limits are computed exactly as 'FINITARY'\'s and are sheaves
-- by the closure instances -- 'TerminalProfunctor', ':*:', and
-- 'Proarrow.Category.Enriched.Finitary.Topos.Reindex' for the equalizers. Its colimits are /not/
-- computed as 'FINITARY'\'s: a quotient of sheaves is no sheaf, so each is the 'FINITARY' colimit
-- with 'Sheafify' applied, and its universal property descends by 'factorLocally', an epi of
-- sheaves being onto only locally. The exponential is 'FINITARY'\'s again, unsheafified. Its
-- hom-sets are finitary by the conjunction instance in
-- "Proarrow.Category.Enriched.Finitary.Topos".
--
-- @'Proarrow.Category.Topos.Omega'@ is 'ClosedSieve', and with it the whole of
-- @'Proarrow.Category.Topos.ElementaryTopos' ('PROD' ('SHEAVES' t j k))@ is above.
type SHEAVES t j k = SUBCAT ((Finitary :&&: Sheaf t) :: OB (j +-> k))

-- | A sheaf as an object of 'SHEAVES', as 'Proarrow.Category.Enriched.Finitary.Topos.FIN' names
-- an object of 'FINITARY'.
type SHF t (p :: j +-> k) = SUB p :: SHEAVES t j k

-- | Equalizers as in 'FINITARY', by 'equalizeNat'; the result is a sheaf for every coverage, which
-- 'Proarrow.Testing.Laws.testEqualizersAreSheaves' checks by enumeration.
instance (Site t k, Enumerable j, Enumerable k) => HasEqualizers (SHEAVES t j k) where
  equalize (Sub (Prof f)) (Sub (Prof g)) k = equalizeNat f g \incl -> k (Sub (Prof incl))
  factorEqualizer (Sub (Prof incl)) (Sub (Prof h)) = Sub (Prof (factorThroughEqualizer incl h))

instance (Site t k, Enumerable j, Enumerable k) => HasPullbacks (SHEAVES t j k)

-- | The colimits are the presheaf colimits, sheafified. Each one is the same three lines: take the
-- 'FINITARY' colimit, follow its cocone with 'unitSheafify', and let 'extendSheafify' do the
-- universal property -- which is exactly the statement that sheafification is a left adjoint, and
-- so preserves the colimits it is applied to.
--
-- The initial sheaf is /not/ the initial presheaf: 'Proarrow.Category.Sheaf.Joins' covers the
-- bottom of a lattice -- the empty set -- by nothing at all, so a sheaf has one section there where the initial presheaf has
-- none, and the sheafification supplies it.
instance (HasFiniteCovers t k, FiniteCat j, FiniteCat k) => HasInitialObject (SHEAVES t j k) where
  type InitialObject @(SHEAVES t j k) = SUB (Sheafify t InitialProfunctor)
  initiate @(SUB q) = case initiate @(j +-> k) @q of Prof n -> Sub (Prof (extendSheafify @t n))

instance (HasFiniteCovers t k, FiniteCat j, FiniteCat k) => HasBinaryCoproducts (SHEAVES t j k) where
  type (||) @(SHEAVES t j k) a b = SUB (Sheafify t (UN SUB a :+: UN SUB b))
  withObCoprod r = r
  lft = Sub (Prof \x -> unitSheafify @t (InjL x))
  rgt = Sub (Prof \y -> unitSheafify @t (InjR y))
  Sub (Prof f) ||| Sub (Prof g) = Sub (Prof (extendSheafify @t \case InjL x -> f x; InjR y -> g y))

-- | The quotient a coequalizer takes is 'coequalizeNat'\'s, sheafified. Its projection is epi in
-- the sheaves but need not be onto -- the sheafification unit is not -- so 'factorCoequalizer' is
-- /not/ 'FINITARY'\'s: it descends, by 'factorThroughLocalEpi'.
instance (HasFiniteCovers t k, FiniteCat j, FiniteCat k) => HasCoequalizers (SHEAVES t j k) where
  coequalize (Sub (Prof @_ @q f)) (Sub (Prof g)) k =
    coequalizeNat f g \ @fs proj ->
      withSheafTables @t @(Sheafify t (Reindex Quotient q fs))
        \toTab _ -> k (Sub (Prof \x -> toTab (unitSheafify @t (proj x))))
  factorCoequalizer (Sub (Prof proj)) (Sub (Prof h)) = Sub (Prof (factorThroughLocalEpi @t proj h))

-- | Not the default coproduct-then-coequalizer: that would sheafify the coproduct and then
-- sheafify the quotient of /that/, and each 'Sheafify' pays for the one under it -- the plus
-- construction re-runs on every 'toIndex'. Taking both steps in 'FINITARY' and sheafifying once
-- at the end is the same object, since sheafification is a left adjoint and preserves the
-- pushout, and on the palette of @Props.Sheaf@ it is the difference between 29 seconds and one.
instance (HasFiniteCovers t k, FiniteCat j, FiniteCat k) => HasPushouts (SHEAVES t j k) where
  pushout (Sub (Prof @_ @a f)) (Sub (Prof @_ @b g)) k =
    coequalizeNat (\x -> InjL (f x)) (\x -> InjR (g x)) \ @fs proj ->
      withSheafTables @t @(Sheafify t (Reindex Quotient (a :+: b) fs))
        \toTab _ ->
          k
            (Sub (Prof \x -> toTab (unitSheafify @t (proj (InjL x)))))
            (Sub (Prof \y -> toTab (unitSheafify @t (proj (InjR y)))))
  factorPushout (Sub (Prof p1)) (Sub (Prof p2)) (Sub (Prof k1)) (Sub (Prof k2)) =
    Sub (Prof (factorThroughLocalEpi @t (\case InjL x -> p1 x; InjR y -> p2 y) (\case InjL x -> k1 x; InjR y -> k2 y)))

-- | The image of an arrow of sheaves, by the same cokernel-pair construction as in 'FINITARY': the
-- pushout is a colimit and so sheafified, the equalizer that follows it is not.
instance (HasFiniteCovers t k, FiniteCat j, FiniteCat k) => HasEpiMonoFactorization (SHEAVES t j k)

-- | The internal hom of a sheaf is a sheaf, and it is the presheaf one -- unlike the colimits,
-- nothing has to be sheafified. It is @q@\'s sheaf condition doing the work, once per point of
-- @p@: a matching family of maps @p -> q@ over a cover of @a@ is a map over @a@ because their
-- values glue in @q@. @p@ needs no condition at all.
--
-- Built rather than found, which is what 'StableSite' buys. The glued map, asked for its value at
-- an arrow @g@ into @a@, pulls the cover back along @g@ and glues the legs\' answers in @q@ --
-- each leg of the pullback factoring through one of the original legs, which is the family entry
-- to ask. Neither @p@ nor @q@ has to be 'Finitary' for that; before 'pullbackCover' this was
-- 'Proarrow.Category.Enriched.Finitary.Topos.glueBySearch' over every element of the exponential,
-- which is an enumeration exponential in the size of @p@, and lawful only by the theorem above.
instance (StableSite t k, Sheaf t q, Profunctor p, CategoryOf j) => Sheaf t (p :~>: q :: j +-> k) where
  glue c m = Exp \g h x ->
    g // h // case pullbackCover c g of
      AlreadyFactors (Factors l u) -> case m l of Exp f -> f u h x
      PulledBack c' factorsThroughLeg -> glue @t c' \l' ->
        case factorsThroughLeg l' of
          Factors l u -> case m l of Exp f -> f u h (lmap (legArrow l') x) \\ legArrow l'

-- | The classifier of the sheaves is the closed sieves, and an arrow classifies the graph sieve
-- 'FINITARY' classifies it by, reflected.
--
-- The reflection is belt and braces: the graph sieve of an arrow /of sheaves/ is closed already.
-- If @'dimap' g h@ of it is covering then @f ('dimap' g h x)@ and @'dimap' g h y@ agree along
-- every leg of a cover, so a separated codomain -- which a sheaf is -- makes them equal, putting
-- @(g, h)@ in the sieve to begin with. What the call guards against is a 'Sheaf' instance
-- asserted rather than decided; without it such an arrow would fail remotely, as 'familyIndex'\'s
-- \"not a closed sieve\".
instance (StableSite t k, HasFiniteCovers t k, FiniteCat j, FiniteCat k) => HasSubobjectClassifier (PROD (SHEAVES t j k)) where
  type Omega @(PROD (SHEAVES t j k)) = PR (SUB (ClosedSieve t))
  true = Prod (Sub (Prof \TerminalProfunctor -> ClosedSieve maximalSieve))
  classifyGraph (Prod (Sub (Prof f))) = Prod (Sub (Prof \(x :*: y) -> closedSieve @t (graphSieve f x y)))

-- | __The topos of sheaves.__ Finite limits and colimits, cartesian closed, a subobject
-- classifier, and image factorization -- each of them above, and none of them postulated.
--
-- 'StableSite' is what the exponential asks for: a full subcategory is closed when it contains
-- its internal homs, and an internal hom is a sheaf by gluing pointwise into the codomain, which
-- needs the cover pulled back along the argument.
instance (StableSite t k, HasFiniteCovers t k, FiniteCat j, FiniteCat k) => ElementaryTopos (PROD (SHEAVES t j k))
