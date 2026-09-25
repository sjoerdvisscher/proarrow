{-# LANGUAGE AllowAmbiguousTypes #-}
-- The instances on 'SHEAVES' are orphans for the reason "Proarrow.Category.Enriched.Finitary.Topos"
-- gives for its own: the kind is 'SUBCAT' of a predicate, and both come from other modules.
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Sheaves on a finite site, decided by enumeration.
--
-- A site is a category where each object @a@ has some /covers/: families of arrows into @a@. A
-- profunctor is a sheaf when an element at @a@ is the same thing as a /matching family/ on a
-- cover: one element at the source of each leg, agreeing wherever two legs overlap. With finitely
-- many objects and elements both sides can be listed, and 'sheafAt' compares the two lists. They
-- must agree as multisets. Equal lengths are not enough: a presheaf can have as many elements as
-- matching families and still not be a sheaf.
--
-- A cover of @a@ generates a 'Sieve', the arrows into @a@ that factor through a leg, and the
-- matching families are the natural transformations out of it ('withSieve').
--
-- The coverage also gives a closure on sieves ('closure', 'lawvereTierney'), truth values
-- ('ClosedSieve') and a sheafification ('Sheafify') with its unit and universal property. All of
-- them are computed, so they too can be enumerated and compared, and together they make 'SHEAVES'
-- an elementary topos.
module Proarrow.Category.Enriched.Finitary.Sheaf where

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
  ( Coverage
  , Factors (..)
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
  , Kind
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

-- | Whether a sieve is the maximal one, containing every arrow of the category.
isMaximal :: forall {j} {k} (a :: k) (b :: j). (FiniteCat j, FiniteCat k) => Sieve a b -> P.Bool
isMaximal s = P.and (sieveTable s)

-- | Whether every point of the second sieve is a point of the first.
contains :: forall {j} {k} (a :: k) (b :: j). (FiniteCat j, FiniteCat k) => Sieve a b -> Sieve a b -> P.Bool
contains s = \s' -> P.and (P.zipWith (\x y -> P.not y P.|| x) ts (sieveTable s'))
  where
    -- tabulated before the second sieve arrives, so a partial application tabulates @s@ once
    ts = sieveTable s

-- | Whether a sieve is covering: either it is the maximal sieve, or it contains the sieve that some
-- cover of its object generates. A sieve is closed under composition, so that amounts to
-- containing the cover's legs ('coveringCover').
--
-- This takes the coverage at face value. It agrees with the Grothendieck topology the coverage
-- generates only when the covers are stable and compose. When they do not, 'closure' stops being
-- idempotent, which 'Proarrow.Testing.Laws.testLawvereTierney' detects.
isCovering
  :: forall t {j} {k} (a :: k) (b :: j)
   . (HasFiniteCovers t k, FiniteCat j, FiniteCat k)
  => Sieve a b
  -> P.Bool
isCovering s = isMaximal s P.|| isJust (coveringCover @t s)

-- | The first listed cover all of whose legs lie in the sieve, if there is one. Both 'isCovering'
-- and 'extendPlus' use this search. It needs no tabulation, since whether a sieve contains the
-- legs at the identity decides whether it contains everything they generate.
--
-- This relies on the closure that "Proarrow.Profunctor.Instance.Sieve" does not enforce. On a
-- hand-built predicate that is not a sieve it can say yes where comparing the whole generated
-- sieve says no.
coveringCover
  :: forall t {j} {k} (a :: k) (b :: j)
   . (HasFiniteCovers t k, CategoryOf j)
  => Sieve a b
  -> P.Maybe (SomeCover t k a)
coveringCover (Sieve s) = find (\(SomeCover c) -> P.all (\(SomeLeg l) -> s (legArrow l) id) (legs c)) (covers @t @k @a)

-- | The Lawvere–Tierney closure of a sieve: the pairs @(g, h)@ along which it pulls back to a
-- covering one. A sieve is covering iff its closure is the maximal sieve.
--
-- This uses @'dimap' g h@, not @'lmap' g@. A coverage constrains only the contravariant side, but
-- a sieve over @j '+->' k@ has two sides, and 'closure' has to be natural in both.
closure
  :: forall t {j} {k} (a :: k) (b :: j)
   . (HasFiniteCovers t k, FiniteCat j, FiniteCat k)
  => Sieve a b
  -> Sieve a b
closure s@Sieve{} = Sieve \g h -> isCovering @t (dimap g h s) \\ g \\ h

-- | Whether a sieve is /closed/ for the topology, i.e. equal to its own 'closure'. These are the
-- truth values of the sheaf topos, as the sieves are of the presheaf one (see 'ClosedSieve').
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
-- the matching families on the sieve it generates, as multisets.
sheafAt
  :: forall t {j} {k} (p :: j +-> k) (a :: k) (b :: j) c
   . (Site t k, Finitary p, FiniteCat j, FiniteCat k, Ob a, Ob b)
  => Cover t k a c
  -> P.Bool
sheafAt c = withSieve (generatedSieve @t @a @b c) \ @q incl ->
  sort [natTable @q @p (\y -> case incl y of Yo g h -> dimap g h x) | x <- elements @p @a @b]
    P.== sort (natElements @q @p)

-- | A sieve as a subobject of the representable @'Yo' a ('OP' b)@, handed on with its inclusion.
-- A natural transformation out of it picks an element for every arrow in the sieve, compatibly
-- with precomposition, which is what a matching family on the sieve is. 'sheafAt' and 'Plus' both
-- define matching families this way.
--
-- The error branch is unreachable for any coverage, since 'generatedSieve' and 'leastDenseSieve'
-- always give real sieves. Reaching it would take a 'Finitary' instance on the hom-profunctor
-- whose 'elements' omits an arrow, which 'Proarrow.Testing.Laws.testFinitary' rules out.
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
-- 'Proarrow.Category.Enriched.Finitary.Topos.withTabulated' does, tagged with the coverage so that
-- it has a 'Sheaf' instance. That instance is decided here by 'isSheaf'; the failure continuation
-- is taken when @p@ is no sheaf for @t@.
--
-- This makes a sheaf with no 'Sheaf' instance of its own (a representable, a sheafification) an
-- object of 'SHEAVES'. Deciding on the tables is also cheaper than on @p@: a 'Sheafify' answers
-- each 'toIndex' by re-running the plus construction.
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

-- | 'withTabulatedSheaf' for a profunctor that already is a 'Sheaf', so there is nothing to decide.
-- The colimits below present their apex, a 'Sheafify', with this, because an unpresented
-- 'Sheafify' re-runs the whole plus construction each time the continuation asks for elements.
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

-- | Extend a /partial/ natural transformation into a sheaf to a total one. Where @f@ is undefined
-- at an element @y@, it must be defined on the restrictions of @y@ along the legs of some listed
-- cover, and those values are glued in @q@. Only this one level of descent is tried.
--
-- 'extendPlus' is this at @'Plus' t p@. The colimits below need it because an epimorphism of
-- sheaves is only /locally/ onto: an element may have no preimage while its restrictions along a
-- cover all do.
--
-- 'glue' is lawful here when @f@ commutes with restriction where it is defined. For the callers
-- below that means the arrow being factored is constant on the fibres it factors through.
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
    -- where the partial function is defined on restrictions of @y@. This is a sieve, since a
    -- restriction of a restriction is one. Taking the element as an argument pins its objects.
    domainSieve :: forall (a :: k) (b :: j). (Ob a, Ob b) => p a b -> Sieve a b
    domainSieve x = Sieve \g _ -> isJust (f (lmap g x)) \\ g

-- | Factor through a map that is onto only locally: @'factorLocally'@ of the preimage search.
-- Where 'Proarrow.Category.Enriched.Finitary.Topos.factorThroughCoequalizer' asks the map to be
-- onto, this asks only what being epi in the sheaves gives.
--
-- A pushout needs this for its pair of injections, which are jointly locally onto but not
-- separately. That case is this at the coproduct, since two arrows into an object are one arrow
-- out of @a ':+:' b@. One search over that is also one 'toIndex' of the element instead of two.
factorThroughLocalEpi
  :: forall t {j} {k} (c :: j +-> k) x c'
   . (HasFiniteCovers t k, CategoryOf j, Finitary c, Finitary x, Sheaf t c')
  => (x :~> c)
  -> (x :~> c')
  -> c :~> c'
factorThroughLocalEpi proj h = factorLocally @t \y -> P.fmap h (preimageMaybe proj y)

-- * Sheafification

-- | One step of the plus construction for the topology @t@. A 'Plus' value is a matching family on
-- some dense sieve, given as a partial function: it is defined at @(g, h)@ iff that pair is in the
-- sieve ('support'), so the sieve cannot disagree with the family. Two values are the same
-- element when they agree on a dense sieve. Intuitively an element at @a@ is an element of @p@
-- given locally: pieces on a cover of @a@ that agree on overlaps.
--
-- On a finite site whose covers compose ('HasFiniteCovers'\'s Composition law) there is a least
-- dense sieve, 'leastDenseSieve', and each element has one family on it. A value is identified by
-- its restriction there ('plusTable'), which is what 'Finitary' numbers and "Proarrow.Testing"
-- compares, so no quotient is needed. 'leastDenseSieve' fails loudly where the law does not hold.
--
-- __The constructor does not check__ that the support is a dense sieve or that the family is
-- matching. 'plusElements' builds only lawful values; one built by hand is its builder's
-- responsibility.
type Plus :: forall {j} {k}. Coverage -> j +-> k -> j +-> k
data Plus t p a b where
  Plus :: (Ob a, Ob b) => (forall c d. c ~> a -> b ~> d -> P.Maybe (p c d)) -> Plus t p a b

instance (CategoryOf j, CategoryOf k) => Profunctor (Plus t p :: j +-> k) where
  dimap l r (Plus f) = l // r // Plus \g h -> f (l . g) (h . r)
  r \\ Plus{} = r

-- | The sieve a value is defined on.
support :: Plus t p :~> Sieve
support (Plus f) = Sieve \g h -> isJust (f g h)

-- | Whether a sieve is dense for the topology: its 'closure' is the maximal sieve. On a lawful
-- coverage this agrees with 'isCovering' ('Proarrow.Testing.Laws.testDenseIsCovering' checks
-- that). But density is the stable notion, and 'Plus' needs stability, since 'dimap' pulls a
-- support back along arrows.
isDense
  :: forall t {j} {k} (a :: k) (b :: j)
   . (HasFiniteCovers t k, FiniteCat j, FiniteCat k)
  => Sieve a b
  -> P.Bool
isDense s = isMaximal (closure @t s)

-- | The meet of all the dense sieves at a pair of objects. When the covers compose, 'closure'
-- preserves meets, so this is the least dense sieve. Restriction to it picks one matching family
-- out of each element of 'Plus'. On a coverage whose covers pull back but do not compose the meet
-- need not be dense, and then this errors, naming the law that failed, instead of letting 'Plus'
-- compute on it. The smallest example is a poset @w ≤ x ≤ a@, @w ≤ y ≤ a@ with @a@ covered by @x@
-- and by @y@ separately and each of those by @w@.
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
-- agree. This builds one sieve for the pair, where two 'plusTable's would each build their own.
-- "Proarrow.Testing"\'s equality on 'Plus' uses it, since it compares far more often than it shows.
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

-- | Sheafification: the plus construction twice. One 'Plus' makes a profunctor /separated/ (two
-- elements with the same restrictions to a dense sieve are equal), and the second makes it a
-- sheaf. The first alone need not: the constant presheaf with two values on the discrete two-point
-- space has one section over the empty set after one plus, but still two over the whole space
-- where a sheaf needs four. On a site whose covers have no overlaps, such as
-- 'Proarrow.Category.Sheaf.Atomic' on the walking arrow, one plus is already a sheaf and the
-- second changes nothing.
type Sheafify :: forall {j} {k}. Coverage -> j +-> k -> j +-> k
type Sheafify t p = Plus t (Plus t p)

-- | The unit of the plus construction: an element as the family of its own restrictions, on the
-- maximal sieve.
unitPlus :: forall t {j} {k} (p :: j +-> k). (Profunctor p) => p :~> Plus t p
unitPlus x = Plus (\g h -> P.Just (dimap g h x)) \\ x

-- | 'unitPlus' twice: the unit of sheafification.
unitSheafify :: forall t {j} {k} (p :: j +-> k). (Profunctor p) => p :~> Sheafify t p
unitSheafify x = unitPlus @t (unitPlus @t x)

-- | The universal property, one plus at a time: a map into a sheaf extends along 'unitPlus'. A
-- dense support is either everything, and then the family is read off at the identity, or it
-- contains the legs of some listed cover (density at the identity says so, and 'coveringCover'
-- finds it), and then the family restricted to those legs glues. Since @q@ is a sheaf, it does not
-- matter which cover is found. @q@ need not be 'Finitary'; only gluing is asked of it.
extendPlus
  :: forall t {j} {k} (p :: j +-> k) q
   . (HasFiniteCovers t k, Sheaf t q)
  => (p :~> q) -> Plus t p :~> q
extendPlus n = factorLocally @t \(Plus f) -> P.fmap n (f id id)

-- | Gluing for the plus construction: a matching family over a cover, assembled into one value.
-- At @(g, h)@ it takes the first leg @l@ with @g = l . u@ ('factorThrough') whose family is
-- defined at @(u, h)@. The support of the result is generated by the legs' supports, so it is dense
-- by 'Proarrow.Category.Sheaf.HasFiniteCovers'\'s Composition law. For a matching family the choice
-- of leg and factorisation does not matter, and 'glue' promises nothing on others.
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

-- | Sheafification lands in the sheaves (@'isSheaf' \@t \@('Sheafify' t p)@ confirms it by
-- enumeration), so a 'Sheafify' can be used wherever a 'Sheaf' is asked for.
--
-- 'gluePlus' is lawful only on a /separated/ @q@, which @'Plus' t p@ always is, hence the double
-- plus in the head. The also true @'Sheaf' t p => 'Sheaf' t ('Plus' t p)@ would overlap this
-- instance with neither more specific.
instance (Site t k, LocallyFinite k, CategoryOf j) => Sheaf t (Sheafify t (p :: j +-> k)) where
  glue = gluePlus @t

-- | 'extendPlus' twice: a map into a sheaf extends along 'unitSheafify'.
extendSheafify
  :: forall t {j} {k} (p :: j +-> k) q
   . (HasFiniteCovers t k, Sheaf t q)
  => (p :~> q) -> Sheafify t p :~> q
extendSheafify n = extendPlus @t (extendPlus @t n)

-- * The truth values of the topos

-- | A sieve equal to its own 'closure'. These are the truth values of the sheaves for @t@, as all
-- sieves are of the presheaves. A subsheaf @s@ of @p@ sends an element @x@ to the sieve of pairs
-- @(g, h)@ with @'dimap' g h x@ in @s@. That sieve is closed: if the restrictions of @x@ along a
-- cover are in @s@, gluing puts @x@ in @s@.
--
-- It is a newtype because the object has to be nameable, and the equalizer of 'lawvereTierney'
-- and the identity on 'Omega' ('equalizeNat') binds its table existentially.
--
-- It is the classifier only when the coverage is a Grothendieck topology ('HasFiniteCovers'\'s
-- Composition law, checked by 'Proarrow.Testing.Laws.testLawvereTierney_'). Otherwise it quietly
-- computes something else, while 'leastDenseSieve' fails loudly.
--
-- __The constructor checks nothing.__ 'elements' produces only closed sieves, and 'closedSieve'
-- closes any sieve.
type ClosedSieve :: forall {j} {k}. Coverage -> j +-> k
newtype ClosedSieve t (a :: k) (b :: j) = ClosedSieve (Sieve a b)

-- | Closure commutes with 'dimap' (the Lawvere–Tierney axiom that 'lawvereTierney' packages as an
-- arrow on 'Omega'), so a restriction of a closed sieve is closed.
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

-- | The classifier is a sheaf, with gluing built directly: the glued sieve contains @g@ iff every
-- leg of the cover pulled back along @g@ is in the sieve of the family member it factors through.
-- Anything in the glued sieve passes this test, since sieves are closed under precomposition, and
-- anything that passes is in it, since the sieves are /closed/.
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

-- | The full subcategory of @'FINITARY' j k@ on the sheaves for @t@. Finite limits and the
-- exponential are 'FINITARY'\'s, and are sheaves by the closure instances ('TerminalProfunctor',
-- ':*:', 'Proarrow.Category.Enriched.Finitary.Topos.Reindex', ':~>:'). Colimits are 'FINITARY'\'s
-- followed by 'Sheafify', since a quotient of sheaves need not be a sheaf, and their universal
-- property uses 'factorLocally', since an epi of sheaves is onto only locally.
-- @'Proarrow.Category.Topos.Omega'@ is 'ClosedSieve'.
type SHEAVES :: Coverage -> Kind -> Kind -> Kind
type SHEAVES t j k = SUBCAT ((Finitary :&&: Sheaf t) :: OB (j +-> k))

-- | A sheaf as an object of 'SHEAVES', as 'Proarrow.Category.Enriched.Finitary.Topos.FIN' names
-- an object of 'FINITARY'.
type SHF :: forall {j} {k}. forall (t :: Coverage) -> (j +-> k) -> SHEAVES t j k
type SHF t (p :: j +-> k) = SUB p :: SHEAVES t j k

-- | Equalizers as in 'FINITARY', by 'equalizeNat'; the result is a sheaf for every coverage, which
-- 'Proarrow.Testing.Laws.testEqualizersAreSheaves' checks by enumeration.
instance (Site t k, Enumerable j, Enumerable k) => HasEqualizers (SHEAVES t j k) where
  equalize (Sub (Prof f)) (Sub (Prof g)) k = equalizeNat f g \incl -> k (Sub (Prof incl))
  factorEqualizer (Sub (Prof incl)) (Sub (Prof h)) = Sub (Prof (factorThroughEqualizer incl h))

instance (Site t k, Enumerable j, Enumerable k) => HasPullbacks (SHEAVES t j k)

-- | Colimits are the presheaf colimits, sheafified: take the 'FINITARY' colimit, follow its cocone
-- with 'unitSheafify', and get the universal property from 'extendSheafify'. This works because
-- sheafification is a left adjoint.
--
-- The initial sheaf need not be the initial presheaf. 'Proarrow.Category.Sheaf.Joins' covers the
-- bottom of a lattice by the empty family, so every sheaf has one section there.
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
-- the sheaves but need not be onto (the sheafification unit is not), so 'factorCoequalizer' is not
-- 'FINITARY'\'s. It descends, by 'factorThroughLocalEpi'.
instance (HasFiniteCovers t k, FiniteCat j, FiniteCat k) => HasCoequalizers (SHEAVES t j k) where
  coequalize (Sub (Prof @_ @q f)) (Sub (Prof g)) k =
    coequalizeNat f g \ @fs proj ->
      withSheafTables @t @(Sheafify t (Reindex Quotient q fs))
        \toTab _ -> k (Sub (Prof \x -> toTab (unitSheafify @t (proj x))))
  factorCoequalizer (Sub (Prof proj)) (Sub (Prof h)) = Sub (Prof (factorThroughLocalEpi @t proj h))

-- | Not the default coproduct-then-coequalizer, which would sheafify the coproduct and then
-- sheafify the quotient of that. Each 'Sheafify' pays for the one under it, since the plus
-- construction re-runs on every 'toIndex'. Taking both steps in 'FINITARY' and sheafifying once
-- at the end gives the same object, since sheafification is a left adjoint and preserves the
-- pushout, and it avoids stacking one plus construction on another.
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

-- | The presheaf internal hom into a sheaf is already a sheaf: a matching family of maps @p -> q@
-- over a cover glues pointwise, because the values glue in @q@. @p@ needs no condition.
--
-- The glued map, at an arrow @g@ into @a@, pulls the cover back along @g@ ('StableSite'). Each
-- pulled-back leg factors through an original leg, whose map is asked, and the answers are glued
-- in @q@. Neither @p@ nor @q@ has to be 'Finitary'. The generic
-- 'Proarrow.Category.Enriched.Finitary.Topos.glueBySearch' would be exponential in the size of @p@.
instance (StableSite t k, Sheaf t q, Profunctor p, CategoryOf j) => Sheaf t (p :~>: q :: j +-> k) where
  glue c m = Exp \g h x ->
    g // h // case pullbackCover c g of
      AlreadyFactors (Factors l u) -> case m l of Exp f -> f u h x
      PulledBack c' factorsThroughLeg -> glue @t c' \l' ->
        case factorsThroughLeg l' of
          Factors l u -> case m l of Exp f -> f u h (lmap (legArrow l') x) \\ legArrow l'

-- | The classifier is the closed sieves, and an arrow is classified by 'FINITARY'\'s graph sieve,
-- closed. For an arrow of sheaves that sieve is already closed, since a sheaf is separated. The
-- 'closedSieve' call guards against a 'Sheaf' instance that was asserted instead of decided, which
-- would otherwise fail later in 'familyIndex' as \"not a closed sieve\".
instance (StableSite t k, HasFiniteCovers t k, FiniteCat j, FiniteCat k) => HasSubobjectClassifier (PROD (SHEAVES t j k)) where
  type Omega @(PROD (SHEAVES t j k)) = PR (SUB (ClosedSieve t))
  true = Prod (Sub (Prof \TerminalProfunctor -> ClosedSieve maximalSieve))
  classifyGraph (Prod (Sub (Prof n))) = Prod (Sub (Prof (closedSieve @t . graphSieve n)))

-- | __The topos of sheaves.__ Finite limits and colimits, cartesian closed, a subobject
-- classifier, and image factorization, all defined above and none of them postulated.
--
-- The exponential needs 'StableSite'. A full subcategory is closed when it contains its internal
-- homs, and an internal hom is a sheaf by gluing pointwise into the codomain, which needs the
-- cover pulled back along the argument.
instance (StableSite t k, HasFiniteCovers t k, FiniteCat j, FiniteCat k) => ElementaryTopos (PROD (SHEAVES t j k))
