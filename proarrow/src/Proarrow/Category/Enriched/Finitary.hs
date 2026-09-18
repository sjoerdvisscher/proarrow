{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Profunctors whose hom-sets are finite and numbered: @p a b@ is in bijection with an initial
-- segment of the naturals. This is the profunctor form of the skeleton of the category of finite
-- sets, and it is what makes limits and colimits computable. An element is an index, so a subset or
-- a quotient of a hom-set is a table of indices, which a computation can produce and reify into a
-- fresh object; an arbitrary profunctor offers no handle on its hom-set other than the type itself.
--
-- The numbering is deliberately a /value/, as in "Proarrow.Category.Instance.FinHask": a size that
-- had to be a type family could only ever be a formula in the sizes it is built from, which rules
-- out every construction whose count depends on how arrows compose -- the exponential and the
-- subobject classifier among them. As values, those are enumerations like any other.
--
-- This is the sibling of "Proarrow.Category.Enriched.Thin", which it builds on: a
-- 'Proarrow.Category.Enriched.Thin.DecidableProfunctor' is the special case where every size is zero
-- or one, its 'Proarrow.Category.Enriched.Thin.Decision' being the pair 'toIndex'\/'fromIndex', and
-- 'decidableSize' and 'decidableFromIndex' build such an instance. As there, the class, the kind
-- wrapper 'FINITARY' and the instances for the basic profunctors all live together here.
module Proarrow.Category.Enriched.Finitary where

import Data.Kind (Constraint)
import Data.List (elemIndex, findIndex, genericIndex, genericLength, genericTake, partition, sort)
import Data.Map.Strict qualified as M
import Data.Proxy (Proxy (..))
import Data.Type.Equality ((:~:) (..))
import Data.Type.Nat (Nat (..), SNatI, reify, snat)
import Data.Type.Nat qualified as N
import Data.Universe.Class qualified as U
import Data.Universe.Helpers qualified as U
import Numeric.Natural (Natural)
import Prelude (Maybe (..), compare, show, ($), (+), (-), (<), (==), (||))
import Prelude qualified as P

import Proarrow.Category.Enriched.Thin
  ( DecidableProfunctor (..)
  , Decision (..)
  , Entry
  , Enumerable (..)
  , Finite (..)
  , Indexed (..)
  , IndexedList (..)
  , KnownList (..)
  )
import Proarrow.Category.Instance.Bool (Booleans)
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Topos
  ( ElementaryTopos
  , HasEpiMonoFactorization (..)
  , HasSubobjectClassifier (..)
  , defaultFactorize
  )
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.Coequalizer (HasCoequalizers (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Colimit.Pushout (HasPushouts)
import Proarrow.Core (CategoryOf (..), Hom, Profunctor (..), Promonad (..), UN, (//), type (+->))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), PROD (..), Prod (..))
import Proarrow.Limit.Equalizer (HasEqualizers (..))
import Proarrow.Limit.Pullback (HasPullbacks)
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Instance.Coproduct ((:+:) (..))
import Proarrow.Profunctor.Instance.Exponential ((:~>:) (..))
import Proarrow.Profunctor.Instance.Initial (InitialProfunctor)
import Proarrow.Profunctor.Instance.Product ((:*:) (..))
import Proarrow.Profunctor.Instance.Sieve (Sieve (..))
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor (..))

-- | A profunctor with finite, numbered hom-sets. 'toIndex' and 'fromIndex' are inverse for indices
-- below 'size'; @fromIndex@ of anything else is an error, as is 'toIndex' of an element that is not
-- one the instance can produce (which only an unlawfully built value can be).
--
-- An instance whose elements are found by searching should define 'elements' and read 'size' off
-- it, rather than let the default call 'fromIndex' once per element and repeat the search each time.
type Finitary :: forall {j} {k}. j +-> k -> Constraint
class (Profunctor p) => Finitary (p :: j +-> k) where
  -- | How many elements the hom-set has.
  size :: (Ob (a :: k), Ob (b :: j)) => Natural

  -- | Where an element sits in 'elements'. Takes its objects like the others do, so that an
  -- instance that has to search can bind the search outside the argument lambda and a caller can
  -- share it with @let toIndexP = 'toIndex' \@p \@a \@b@.
  toIndex :: (Ob (a :: k), Ob (b :: j)) => p a b -> Natural

  -- | The element at a position.
  fromIndex :: (Ob (a :: k), Ob (b :: j)) => Natural -> p a b

  -- | All elements of a hom-set, in index order.
  elements :: (Ob (a :: k), Ob (b :: j)) => [p a b]
  elements @a @b = P.map (fromIndex @p) (indices (size @p @a @b))

-- | The subcategory of finitary profunctors, as "Proarrow.Category.Instance.Rep" does for
-- representable ones.
type FINITARY j k = SUBCAT (Finitary :: (j +-> k) -> Constraint)

type FIN (p :: j +-> k) = SUB p :: FINITARY j k

-- | @[0 .. n-1]@, which @n@ being a 'Natural' rules out writing directly.
indices :: Natural -> [Natural]
indices n = genericTake n [0 ..]

-- | The position of an object in its kind's object list.
objIndex :: forall {k} (a :: k). (Enumerable k, Ob a) => Natural
objIndex = withIndex @k @a (N.snatToNatural (snat @(Index a)))

-- | Everything an enumeration of a kind's objects can do at each of them, concatenated.
foreachOb :: forall k r. (Enumerable k) => (forall (a :: k). (Ob a) => [r]) -> [r]
foreachOb f = go (finite @k)
  where
    go :: forall (as :: [k]). IndexedList as -> [r]
    go FNil = []
    go (FCons @a as) = withOb @k @a (f @a) P.++ go as

-- * Thin profunctors

-- | A decidable profunctor has one element where it holds and none where it does not. These cannot
-- be @default@ method bodies: 'size' and 'fromIndex' do not mention their objects except in a
-- constraint, so GHC cannot tie a default body's objects to the instance's.
decidableSize :: forall {j} {k} (p :: j +-> k) (a :: k) (b :: j). (DecidableProfunctor p, Ob a, Ob b) => Natural
decidableSize = case decide @p @a @b of
  Yes _ -> 1
  No -> 0

decidableFromIndex
  :: forall {j} {k} (p :: j +-> k) (a :: k) (b :: j). (DecidableProfunctor p, Ob a, Ob b) => Natural -> p a b
decidableFromIndex _ = case decide @p @a @b of
  Yes x -> x
  No -> P.error "fromIndex: the profunctor does not hold here"

-- * Hom-sets as finite sets

-- | An element of a hom-set of @p@, viewed as an element of a /finite set/: every instance the
-- @universe@ package asks for is supplied by the numbering, with 'toIndex' standing in for equality
-- and ordering. This is what makes a finitary profunctor a profunctor enriched in
-- 'Proarrow.Category.Instance.FinHask.FINHASK' -- see its
-- @'Proarrow.Category.Enriched.EnrichedProfunctor' FINHASK@
-- instance -- exactly as a decided profunctor is one enriched in
-- 'Proarrow.Category.Instance.Bool.BOOL'.
newtype Elt (p :: j +-> k) (a :: k) (b :: j) = Elt {unElt :: p a b}

instance (Finitary p, Ob a, Ob b) => U.Universe (Elt (p :: j +-> k) a b) where
  universe = P.map Elt (elements @p)

instance (Finitary p, Ob a, Ob b) => U.Finite (Elt (p :: j +-> k) a b) where
  cardinality = U.Tagged (size @p @a @b)

instance (Finitary p) => P.Eq (Elt (p :: j +-> k) a b) where
  Elt x == Elt y = (toIndex x == toIndex y) \\ x

instance (Finitary p) => P.Ord (Elt (p :: j +-> k) a b) where
  compare (Elt x) (Elt y) = P.compare (toIndex x) (toIndex y) \\ x

-- | Its 'P.Eq' and 'P.Ord' cost whatever 'toIndex' costs, so an instance intended for enrichment
-- should compute 'toIndex' directly rather than by searching 'elements' -- 'finiteToIndex' searches,
-- which is fine for small hom-sets and not for large ones.

-- | The index, there being nothing else to show: a hom-set of a finitary profunctor is known only up
-- to its numbering.
instance (Finitary p) => P.Show (Elt (p :: j +-> k) a b) where
  show (Elt x) = P.show (toIndex x) \\ x

-- | A category whose hom-sets are finite: the 'Finitary' counterpart of
-- 'Proarrow.Category.Enriched.Thin.Decidable', and one half of 'FiniteCat'.
class (CategoryOf k, Finitary (Hom k)) => LocallyFinite k

instance (CategoryOf k, Finitary (Hom k)) => LocallyFinite k

-- | A profunctor between categories with finite hom-sets is finitary exactly when it is enriched in
-- finite sets, so a 'Finitary' instance can be read off an enrichment as well as the other way
-- round: these are the counterparts of 'decidableSize' and 'decidableFromIndex' one level up.
--
-- 'finiteToIndex' and 'finiteFromIndex' number a hom-set by /searching/ its 'U.universeF', which is
-- all a bare 'U.Finite' instance allows. That is fine for small hom-sets, and an instance whose
-- hom-sets are large should compute the index arithmetically instead --
-- 'Proarrow.Category.Instance.FinHask.FinHask' does, because 'Elt'\'s 'P.Ord' is @'P.compare'@ on
-- indices and so pays for every comparison.
finiteSize :: forall {j} {k} (p :: j +-> k) (a :: k) (b :: j). (U.Finite (p a b)) => Natural
finiteSize = U.unTagged (U.cardinality @(p a b))

finiteToIndex :: forall {j} {k} (p :: j +-> k) (a :: k) (b :: j). (U.Finite (p a b), P.Eq (p a b)) => p a b -> Natural
finiteToIndex x = case elemIndex x U.universeF of
  Just i -> P.fromIntegral i
  Nothing -> P.error "toIndex: not in the universe of the hom-set"

finiteFromIndex :: forall {j} {k} (p :: j +-> k) (a :: k) (b :: j). (U.Finite (p a b)) => Natural -> p a b
finiteFromIndex i = genericIndex (U.universeF @(p a b)) i

-- | The one-object category has one arrow.
instance Finitary Unit where
  size = 1
  toIndex Unit = 0
  fromIndex _ = Unit

-- | @'Proarrow.Category.Instance.Bool.BOOL'@ is thin, so each hom-set holds at most the one arrow.
instance Finitary Booleans where
  size @a @b = decidableSize @Booleans @a @b
  toIndex _ = 0
  fromIndex @a @b = decidableFromIndex @Booleans @a @b

-- * Products and coproducts

-- | The terminal profunctor has one element everywhere.
instance (CategoryOf j, CategoryOf k) => Finitary (TerminalProfunctor :: j +-> k) where
  size = 1
  toIndex TerminalProfunctor = 0
  fromIndex _ = TerminalProfunctor

-- | A pair of indices as one index, row-major: @i * 'size' \@q + j@.
instance (Finitary p, Finitary q) => Finitary (p :*: q) where
  size @a @b = size @p @a @b P.* size @q @a @b
  toIndex @a @b (x :*: y) = toIndex x P.* size @q @a @b + toIndex y
  fromIndex @a @b i = case size @q @a @b of
    0 -> P.error "fromIndex: a factor of the product has no elements"
    n -> let (l, r) = i `P.divMod` n in fromIndex l :*: fromIndex r

-- | The initial profunctor has no elements anywhere.
instance (CategoryOf j, CategoryOf k) => Finitary (InitialProfunctor :: j +-> k) where
  size = 0
  toIndex = \case {}
  fromIndex _ = P.error "fromIndex: the initial profunctor has no elements"

-- | The indices of @p@ first, then those of @q@.
instance (Finitary p, Finitary q) => Finitary (p :+: q) where
  size @a @b = size @p @a @b + size @q @a @b
  toIndex @a @b = \case
    InjL x -> toIndex x
    InjR y -> size @p @a @b + toIndex y
  fromIndex @a @b i = if i < size @p @a @b then InjL (fromIndex i) else InjR (fromIndex (i - size @p @a @b))

instance (CategoryOf j, CategoryOf k) => HasTerminalObject (FINITARY j k) where
  type TerminalObject = FIN TerminalProfunctor
  terminate = Sub terminate

instance (CategoryOf j, CategoryOf k) => HasBinaryProducts (FINITARY j k) where
  type a && b = SUB (UN SUB a :*: UN SUB b)
  withObProd r = r
  fst @(SUB p) @(SUB q) = Sub (fst @(j +-> k) @p @q)
  snd @(SUB p) @(SUB q) = Sub (snd @(j +-> k) @p @q)
  Sub l &&& Sub r = Sub (l &&& r)

instance (CategoryOf j, CategoryOf k) => HasInitialObject (FINITARY j k) where
  type InitialObject = FIN InitialProfunctor
  initiate = Sub initiate

instance (CategoryOf j, CategoryOf k) => HasBinaryCoproducts (FINITARY j k) where
  type a || b = SUB (UN SUB a :+: UN SUB b)
  withObCoprod r = r
  lft @(SUB p) @(SUB q) = Sub (lft @(j +-> k) @p @q)
  rgt @(SUB p) @(SUB q) = Sub (rgt @(j +-> k) @p @q)
  Sub l ||| Sub r = Sub (l ||| r)

-- * Tables of fibres

-- | A type-level list of naturals, reflected.
class KnownNats (ns :: [Nat]) where
  natsVal :: [Natural]

instance KnownNats '[] where
  natsVal = []

instance (SNatI n, KnownNats ns) => KnownNats (n ': ns) where
  natsVal = N.snatToNatural (snat @n) : natsVal @ns

-- | A type-level list of lists of naturals, reflected: the fibres of a partial surjection out of
-- one hom-set.
class KnownFibres (fs :: [[Nat]]) where
  fibresVal :: [[Natural]]

instance KnownFibres '[] where
  fibresVal = []

instance (KnownNats f, KnownFibres fs) => KnownFibres (f ': fs) where
  fibresVal = natsVal @f : fibresVal @fs

-- | Reify a list of lists of naturals.
fibres :: forall r. [[Natural]] -> (forall fs. (KnownFibres fs) => r) -> r
fibres [] k = k @'[]
fibres (f : fs) k = nats f \ @f' -> fibres fs \ @fs' -> k @(f' ': fs')
  where
    nats :: forall r'. [Natural] -> (forall ns. (KnownNats ns) => r') -> r'
    nats [] k' = k' @'[]
    nats (n : ns) k' = reify (N.fromNatural n) \(_ :: Proxy n) -> nats ns \ @ns' -> k' @(n ': ns')

-- | A table: a row for each object of @k@, and in each row the fibres at each object of @j@.
type KnownTable bs as t = KnownList (KnownList KnownFibres bs) as t

-- | Build a table by visiting every pair of objects, reifying each cell.
buildTable
  :: forall j k r
   . (Enumerable j, Enumerable k)
  => (forall (a :: k) (b :: j). (Ob a, Ob b) => [[Natural]])
  -> (forall (t :: [[[[Nat]]]]). (KnownTable (Objects j) (Objects k) t) => r)
  -> r
buildTable cell = rows (finite @k)
  where
    rows :: forall (as :: [k]) r'. IndexedList as -> (forall t. (KnownTable (Objects j) as t) => r') -> r'
    rows FNil k' = k' @'[]
    rows (FCons @a as) k' = withOb @k @a (row @a (finite @j) \ @r0 -> rows as \ @t -> k' @(r0 ': t))
    row
      :: forall (a :: k) (bs :: [j]) r'. (Ob a) => IndexedList bs -> (forall r0. (KnownList KnownFibres bs r0) => r') -> r'
    row FNil k' = k' @'[]
    row (FCons @b bs) k' = withOb @j @b (fibres (cell @a @b) \ @fs -> row @a bs \ @r0 -> k' @(fs ': r0))

-- * Reindexing along a table of fibres

-- | @p@ relabelled, at each pair of objects, along a partial surjection onto an initial segment of
-- the naturals, given by its fibres: index @i@ of the new hom-set stands for the elements of @p@ in
-- the @i@-th fibre. Singleton fibres cut out a subobject, a partition is a quotient. Well behaved
-- exactly when the fibres are respected by @p@'s 'dimap', which is the case for the tables
-- 'equalize' and 'coequalize' build; 'dimap' delegates to @p@ and relies on it.
newtype Reindex (p :: j +-> k) (fs :: [[[[Nat]]]]) (a :: k) (b :: j) = Reindex (p a b)

type Cell fs (a :: k) (b :: j) = Entry (Entry fs (Index a)) (Index b)

instance (Profunctor p) => Profunctor (Reindex p fs) where
  dimap l r (Reindex x) = Reindex (dimap l r x)
  r \\ Reindex x = r \\ x

-- | The fibres at a pair of objects, found by walking the table to the objects' positions.
withCell
  :: forall {j} {k} fs (a :: k) (b :: j) r
   . (Enumerable j, Enumerable k, KnownTable (Objects j) (Objects k) fs, Ob a, Ob b)
  => ((KnownFibres (Cell fs a b)) => r) -> r
withCell r =
  withIndex @k @a $
    withIndex @j @b $
      withAtLookup @k (snat @(Index a)) $
        withAtLookup @j (snat @(Index b)) $
          withEntry @(KnownList KnownFibres (Objects j)) @(Objects k) @fs (snat @(Index a)) Refl $
            withEntry @KnownFibres @(Objects j) @(Entry fs (Index a)) (snat @(Index b)) Refl r

instance
  (Finitary p, Enumerable j, Enumerable k, KnownTable (Objects j) (Objects k) fs)
  => Finitary (Reindex (p :: j +-> k) fs)
  where
  size @a @b = withCell @fs @a @b (genericLength (fibresVal @(Cell fs a b)))
  toIndex @a @b (Reindex x) =
    withCell @fs @a @b
      ( case findIndex (P.elem (toIndex x)) (fibresVal @(Cell fs a b)) of
          Just pos -> P.fromIntegral pos
          Nothing -> P.error "Reindex: element outside every fibre"
      )
      \\ x
  fromIndex @a @b i =
    withCell @fs @a @b $
      case genericIndex (fibresVal @(Cell fs a b)) i of
        rep : _ -> Reindex (fromIndex @p rep)
        [] -> P.error "Reindex: empty fibre"

-- * Equalizers and coequalizers

-- | The element of @p@ that @f@ sends to a given element of @q@, when @f@ is injective and the
-- element is in its image -- which is what both factorizations below need, in opposite directions.
preimage
  :: forall {j} {k} (p :: j +-> k) q (a :: k) (b :: j)
   . (Finitary p, Finitary q, Ob a, Ob b)
  => P.String -> (p a b -> q a b) -> q a b -> p a b
preimage msg f y =
  let toIndexQ = toIndex @q @a @b
  in case [x | x <- elements @p @a @b, toIndexQ (f x) == toIndexQ y] of
       x : _ -> x
       [] -> P.error msg

-- | Partition a list of indices into the equivalence classes generated by a list of pairs. Both
-- levels are sorted, so the classes come out ordered by their least member and the table is canonical.
classes :: [(Natural, Natural)] -> [Natural] -> [[Natural]]
classes pairs is = sort (P.map sort (P.foldr merge (P.map (: []) is) pairs))
  where
    merge (i, j) cs = case partition (\c -> P.elem i c || P.elem j c) cs of
      ([], _) -> P.error "classes: an index outside the set being partitioned"
      (hit, miss) -> P.concat hit : miss

-- | Equalizers of finitary profunctors between finite categories: at each pair of objects, keep the
-- indices on which the two natural transformations agree, and reify the table.
instance (Enumerable j, Enumerable k) => HasEqualizers (FINITARY j k) where
  equalize (Sub (Prof @p @q f)) (Sub (Prof g)) k =
    buildTable @j @k
      ( \ @a @b ->
          let toIndexP = toIndex @p @a @b; toIndexQ = toIndex @q @a @b
          in [[toIndexP x] | x <- elements @p @a @b, toIndexQ (f x) == toIndexQ (g x)]
      )
      \ @fs -> k (Sub (Prof @(Reindex p fs) \(Reindex x) -> x))
  factorEqualizer (Sub (Prof @e incl)) (Sub (Prof @e' h)) =
    Sub (Prof @e' @e \y -> preimage "factorEqualizer: h's image must lie within incl's image" incl (h y) \\ y)

-- | Coequalizers: at each pair of objects, partition the indices by the equivalence relation the two
-- natural transformations generate, and reify the table. Naturality makes the partition a
-- congruence, so the quotient is again a profunctor.
instance (Enumerable j, Enumerable k) => HasCoequalizers (FINITARY j k) where
  coequalize (Sub (Prof @p @q f)) (Sub (Prof g)) k =
    buildTable @j @k
      ( \ @a @b ->
          let toIndexQ = toIndex @q @a @b
          in classes [(toIndexQ (f x), toIndexQ (g x)) | x <- elements @p @a @b] (P.map toIndexQ (elements @q @a @b))
      )
      \ @fs -> k (Sub (Prof @q @(Reindex q fs) Reindex))
  factorCoequalizer (Sub (Prof @_ @c proj)) (Sub (Prof @_ @c' h)) =
    Sub (Prof @c @c' \y -> h (preimage "factorCoequalizer: proj must be onto" proj y) \\ y)

-- * Pullbacks, pushouts and images

-- | Pullbacks are equalizers of products, and pushouts coequalizers of coproducts, all of which
-- finitary profunctors have.
instance (Enumerable j, Enumerable k) => HasPullbacks (FINITARY j k)

instance (Enumerable j, Enumerable k) => HasPushouts (FINITARY j k)

-- | The image of a natural transformation is the equalizer of its cokernel pair.
instance (Enumerable j, Enumerable k) => HasEpiMonoFactorization (FINITARY j k) where
  factorize = defaultFactorize

-- * Ends by enumeration

-- | A finite category: finitely many objects, and finitely many arrows between them. The first is
-- 'Enumerable', the second does not follow from it, and the ends below need both.
class (Enumerable k, Finitary (Hom k)) => FiniteCat k

instance (Enumerable k, Finitary (Hom k)) => FiniteCat k

-- | One point of the domain of an end at @a@\/@b@, as a key into a tabulated family: an object
-- pair and, there, an arrow into @a@, an arrow out of @b@ and an element of @p@.
type EndKey = (Natural, Natural, Natural, Natural, Natural)

-- | Visit every point of that domain, in one fixed order. Everything that tabulates or reads a
-- family walks it with this, so that a family is a list of values in this order.
endDomain
  :: forall {j} {k} (p :: j +-> k) (a :: k) (b :: j) r
   . (Finitary p, FiniteCat j, FiniteCat k, Ob a, Ob b)
  => (forall c d. (Ob c, Ob d) => c ~> a -> b ~> d -> p c d -> r)
  -> [r]
endDomain f =
  foreachOb @k \ @c ->
    foreachOb @j \ @d ->
      -- Bound outside the comprehension so that each is enumerated once, not once per outer choice.
      let cas = elements @(Hom k) @c @a; bds = elements @(Hom j) @b @d; xs = elements @p @c @d
      in [f ca bd x | ca <- cas, bd <- bds, x <- xs]

endKey
  :: forall {j} {k} (c :: k) (d :: j) (p :: j +-> k) a b
   . (FiniteCat j, FiniteCat k, Finitary p, Ob c, Ob d)
  => c ~> a -> b ~> d -> p c d -> EndKey
endKey ca bd x = ca // bd // (objIndex @c, objIndex @d, toIndex ca, toIndex bd, toIndex x)

-- | Where each key sits in a tabulated family.
endPositions
  :: forall {j} {k} (p :: j +-> k) (a :: k) (b :: j)
   . (Finitary p, FiniteCat j, FiniteCat k, Ob a, Ob b)
  => M.Map EndKey P.Int
endPositions = M.fromList (P.zip (endDomain @p @a @b @EndKey endKey) [0 ..])

-- | The naturality conditions on a family: at each pair of arrows @g@, @h@, the point a given point
-- is carried to, and the transport of @q@\'s indices that the family must commute with. The
-- transport is a table rather than a function, so that @q@ is enumerated once per condition.
endLaws
  :: forall {j} {k} (p :: j +-> k) (q :: j +-> k) (a :: k) (b :: j)
   . (Finitary p, Finitary q, FiniteCat j, FiniteCat k, Ob a, Ob b)
  => [(EndKey, EndKey, [Natural])]
endLaws =
  foreachOb @k \ @c ->
    foreachOb @j \ @d ->
      foreachOb @k \ @c' ->
        foreachOb @j \ @d' ->
          let gs = elements @(Hom k) @c' @c
              hs = elements @(Hom j) @d @d'
              cas = elements @(Hom k) @c @a
              bds = elements @(Hom j) @b @d
              xs = elements @p @c @d
          in [ (endKey ca bd x, endKey (ca . g) (h . bd) (dimap g h x), P.map (toIndex . dimap g h) (elements @q @c @d))
             | g <- gs
             , h <- hs
             , ca <- cas
             , bd <- bds
             , x <- xs
             ]

-- | Enumerate an end by brute force: every way of choosing a value at each point of the domain,
-- kept when it satisfies every condition. The candidate space is the product of the choices over
-- the whole domain, so this is only ever run on small categories.
endElements :: [[v]] -> [(P.Int, P.Int, v -> v -> P.Bool)] -> [[v]]
endElements choices laws = P.filter ok (P.sequence choices)
  where
    ok t = P.all (\(src, tgt, rel) -> rel (genericIndex t src) (genericIndex t tgt)) laws

-- | Every natural family, as its list of @q@-indices in 'endDomain' order.
expElements
  :: forall {j} {k} (p :: j +-> k) (q :: j +-> k) (a :: k) (b :: j)
   . (Finitary p, Finitary q, FiniteCat j, FiniteCat k, Ob a, Ob b)
  => [[Natural]]
expElements =
  endElements
    (endDomain @p @a @b \ @c @d _ _ _ -> indices (size @q @c @d))
    [(at src, at tgt, \i j -> j == genericIndex tr i) | (src, tgt, tr) <- endLaws @p @q @a @b]
  where
    at = (endPositions @p @a @b M.!)

-- | Read a tabulated family back as a function on the keys.
atKey
  :: forall {j} {k} (p :: j +-> k) (a :: k) (b :: j) v
   . (Finitary p, FiniteCat j, FiniteCat k, Ob a, Ob b)
  => [v] -> EndKey -> v
atKey row = (M.fromList (P.zip (endDomain @p @a @b @EndKey endKey) row) M.!)

-- | Which of the enumerated families a tabulated one is.
familyIndex :: (P.Eq v) => P.String -> [[v]] -> [v] -> Natural
familyIndex msg fams row = case elemIndex row fams of
  Just i -> P.fromIntegral i
  Nothing -> P.error msg

-- | The internal hom of finitary profunctors is finitary: its elements are the natural families,
-- enumerated. Nothing here is a formula in the sizes of @p@ and @q@ -- the count depends on how the
-- arrows of @j@ and @k@ compose -- which is why 'size' is a value and not a type family.
instance (Finitary p, Finitary q, FiniteCat j, FiniteCat k) => Finitary (p :~>: q :: j +-> k) where
  size @a @b = genericLength (expElements @p @q @a @b)
  toIndex @a @b = \(Exp f) -> familyIndex "toIndex: the family is not natural" es (endDomain @p @a @b \ca bd x -> toIndex (f ca bd x))
    where
      es = expElements @p @q @a @b
  fromIndex @a @b i =
    let at = atKey @p @a @b (genericIndex (expElements @p @q @a @b) i)
    in Exp \ca bd x -> ca // bd // fromIndex @q (at (endKey ca bd x))
  elements @a @b =
    P.map
      (\row -> let at = atKey @p @a @b row in Exp \ca bd x -> ca // bd // fromIndex @q (at (endKey ca bd x)))
      (expElements @p @q @a @b)

-- | Finitary profunctors are cartesian closed. The 'PROD' wrapper is what makes the tensor the
-- product rather than Day convolution, exactly as it does for @j '+->' k@ itself.
instance (FiniteCat j, FiniteCat k) => Closed (PROD (FINITARY j k)) where
  type p ~~> q = PR (SUB (UN SUB (UN PR p) :~>: UN SUB (UN PR q)))
  withObExp r = r
  curry (Prod (Sub (Prof n))) = Prod (Sub (Prof \p -> p // Exp \ca bd q -> n (dimap ca bd p :*: q)))
  apply = Prod (Sub (Prof \(Exp f :*: q) -> f id id q \\ q))
  Prod (Sub (Prof m)) ^^^ Prod (Sub (Prof n)) = Prod (Sub (Prof \(Exp f) -> Exp \ca bd p -> m (f ca bd (n p))))

-- * The subobject classifier

-- | Every sieve, as the points of the representable it contains, in 'endDomain' order: all subsets,
-- kept when closed. The representable at @a@\/@b@ is the domain of the end at the terminal object,
-- and the closure conditions are that end's naturality conditions read as implications.
sieveElements :: forall {j} {k} (a :: k) (b :: j). (FiniteCat j, FiniteCat k, Ob a, Ob b) => [[P.Bool]]
sieveElements =
  endElements
    (endDomain @TerminalProfunctor @a @b \_ _ _ -> [P.False, P.True])
    [(at src, at tgt, \s t -> P.not s P.|| t) | (src, tgt, _) <- endLaws @TerminalProfunctor @TerminalProfunctor @a @b]
  where
    at = (endPositions @TerminalProfunctor @a @b M.!)

instance (FiniteCat j, FiniteCat k) => Finitary (Sieve :: j +-> k) where
  size @a @b = genericLength (sieveElements @a @b)
  toIndex @a @b = \(Sieve s) -> familyIndex "toIndex: not a sieve" es (endDomain @TerminalProfunctor @a @b \ca bd _ -> s ca bd)
    where
      es = sieveElements @a @b
  fromIndex @a @b i = sieveAt (genericIndex (sieveElements @a @b) i)
  elements @a @b = P.map sieveAt (sieveElements @a @b)

-- | A tabulated sieve as a sieve.
sieveAt :: forall {j} {k} (a :: k) (b :: j). (FiniteCat j, FiniteCat k, Ob a, Ob b) => [P.Bool] -> Sieve a b
sieveAt row =
  let at = atKey @TerminalProfunctor @a @b row
  in Sieve \ca bd -> ca // bd // at (endKey ca bd TerminalProfunctor)

-- | The subobject classifier is the profunctor of sieves, and an arrow classifies its graph: the
-- sieve of all the ways an element of @p@ and one of @q@ can be carried to a matching pair.
instance (FiniteCat j, FiniteCat k) => HasSubobjectClassifier (PROD (FINITARY j k)) where
  type Omega = PR (SUB Sieve)
  true = Prod (Sub (Prof \TerminalProfunctor -> Sieve \_ _ -> P.True))
  classifyGraph (Prod (Sub (Prof @_ @q f))) =
    Prod (Sub (Prof \(x :*: y) -> x // Sieve \g h -> g // h // toIndex @q (f (dimap g h x)) == toIndex (dimap g h y)))

-- | Finitary profunctors between finite categories form an elementary topos: finite limits and
-- colimits, cartesian closed, a subobject classifier, and image factorization.
instance (FiniteCat j, FiniteCat k) => ElementaryTopos (PROD (FINITARY j k))
