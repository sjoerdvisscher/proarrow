{-# LANGUAGE AllowAmbiguousTypes #-}
-- Orphans throughout, and unavoidably: every instance here is on either 'SUBCAT' 'Finitary' (the
-- kind synonym 'FINITARY' expands to it, and both halves of that come from other modules) or on a
-- profunctor defined elsewhere. Both the class and the category it carves out have to sit below the
-- enrichment machinery; everything computed in that category needs things sitting above it.
{-# OPTIONS_GHC -Wno-orphans #-}

-- | __The topos of finitary profunctors.__ Everything built on the numbering in
-- "Proarrow.Category.Enriched.Finitary": a hom-set is an initial segment of the naturals, so a
-- subobject or a quotient of one is a table of indices, and a computation can produce such a table
-- and reify it into a fresh object. That is 'Reindex', and it gives equalizers, coequalizers,
-- pullbacks, pushouts and epi-mono factorization.
--
-- The internal hom and the subobject classifier are the same construction one level up: both are
-- ends, enumerated by choosing a value at every point of a domain and keeping the choices that
-- commute with the action. Neither count is a formula in the sizes it is built from -- they depend
-- on how the arrows of @j@ and @k@ compose -- which is exactly why the numbering is a value.
--
-- The punchline is @'ElementaryTopos' ('PROD' ('FINITARY' j k))@ at the end. 'PROD' is what makes
-- the tensor the product rather than Day convolution, as it does for @j '+->' k@ itself.
module Proarrow.Category.Enriched.Finitary.Topos where

import Data.IntMap.Strict qualified as IM
import Data.Kind (Constraint, Type)
import Data.List (elemIndex, findIndex, genericIndex, genericLength, genericReplicate, partition, sort)
import Data.Map.Strict qualified as M
import Data.Proxy (Proxy (..))
import Data.Type.Equality ((:~:) (..))
import Data.Type.Nat (Nat (..), SNatI, reify, snat)
import Data.Type.Nat qualified as N
import Numeric.Natural (Natural)
import Prelude (Maybe (..), ($), (==), (||), type (~))
import Prelude qualified as P

import Proarrow.Category.Enriched.Finitary
import Proarrow.Category.Enriched.Thin
  ( Entry
  , Enumerable (..)
  , Finite (..)
  , Indexed (..)
  , IndexedList (..)
  , KnownList (..)
  )
import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Sheaf (Sheaf (..), Site (..), SomeLeg (..), Trivial)
import Proarrow.Category.Topos
  ( ElementaryTopos
  , HasEpiMonoFactorization (..)
  , HasSubobjectClassifier (..)
  )
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.Coequalizer (HasCoequalizers (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Colimit.Pushout (HasPushouts)
import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Hom
  , OB
  , Profunctor (..)
  , Promonad (..)
  , UN
  , lmap
  , rmap
  , (//)
  , type (+->)
  , type (:~>)
  )
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), PROD (..), Prod (..))
import Proarrow.Limit.Equalizer (HasEqualizers (..))
import Proarrow.Limit.Pullback (HasPullbacks)
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Instance.Coproduct ((:+:) (..))
import Proarrow.Profunctor.Instance.Exponential ((:~>:) (..))
import Proarrow.Profunctor.Instance.Initial (InitialProfunctor)
import Proarrow.Profunctor.Instance.Product ((:*:) (..))
import Proarrow.Profunctor.Instance.Sieve (Sieve (..), maximalSieve)
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor (..))
import Proarrow.Profunctor.Instance.Yoneda (Yo (..))

-- | The subcategory of finitary profunctors, as "Proarrow.Category.Instance.Rep" does for
-- representable ones.
type FINITARY j k = SUBCAT (Finitary :: (j +-> k) -> Constraint)

type FIN (p :: j +-> k) = SUB p :: FINITARY j k

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

-- | What a table of fibres does to the profunctor it relabels. The relabelling is the same either
-- way; what differs is what may be concluded from it, and that is why this is in the type at all --
-- see the 'Sheaf' instance below, which is for 'Subobject' alone.
--
-- ['Subobject'] singleton fibres: the elements kept, renumbered. What 'withSubobject' and
--   'equalizeNat' build.
--
-- ['Quotient'] a partition: one index per class of a congruence. What 'coequalize' builds.
type Retabulation :: Type
type data Retabulation = Subobject | Quotient

-- | @p@ relabelled, at each pair of objects, along a partial surjection onto an initial segment of
-- the naturals, given by its fibres: index @i@ of the new hom-set stands for the elements of @p@ in
-- the @i@-th fibre. Well behaved exactly when the fibres are respected by @p@'s 'dimap', which is
-- the case for the tables 'equalize' and 'coequalize' build; 'dimap' delegates to @p@ and relies on
-- it.
type Reindex :: forall {j} {k}. Retabulation -> (j +-> k) -> [[[[Nat]]]] -> j +-> k
newtype Reindex r p fs a b = Reindex (p a b)

type Cell fs (a :: k) (b :: j) = Entry (Entry fs (Index a)) (Index b)

instance (Profunctor p) => Profunctor (Reindex r p fs) where
  dimap l r (Reindex x) = Reindex (dimap l r x)
  r \\ Reindex x = r \\ x

-- | The fibres at a pair of objects, found by walking the table to the objects' positions.
cellVal
  :: forall {j} {k} fs (a :: k) (b :: j)
   . (Enumerable j, Enumerable k, KnownTable (Objects j) (Objects k) fs, Ob a, Ob b)
  => [[Natural]]
cellVal =
  withIndex @k @a $
    withIndex @j @b $
      withAtLookup @k (snat @(Index a)) $
        withAtLookup @j (snat @(Index b)) $
          withEntry @(KnownList KnownFibres (Objects j)) @(Objects k) @fs (snat @(Index a)) Refl $
            withEntry @KnownFibres @(Objects j) @(Entry fs (Index a)) (snat @(Index b)) Refl $
              fibresVal @(Cell fs a b)

instance
  (Finitary p, Enumerable j, Enumerable k, KnownTable (Objects j) (Objects k) fs)
  => Finitary (Reindex r (p :: j +-> k) fs)
  where
  size @a @b = genericLength (cellVal @fs @a @b)
  toIndex @a @b (Reindex x) =
    ( case findIndex (P.elem (toIndex x)) (cellVal @fs @a @b) of
        Just pos -> P.fromIntegral pos
        Nothing -> P.error "Reindex: element outside every fibre"
    )
      \\ x
  fromIndex @a @b i = case genericIndex (cellVal @fs @a @b) i of
    rep : _ -> Reindex (fromIndex @p rep)
    [] -> P.error "Reindex: empty fibre"

-- | A retabulation of a sheaf glues as the sheaf does -- for a 'Subobject' table. Not for a
-- 'Quotient' one, where 'glue' would not even be well defined: it would read a class through
-- whichever representative it was handed, and the element it glues need not be in the class the
-- family came from. A quotient of a sheaf is no sheaf, which is why colimits of sheaves go through
-- sheafification -- and why the marker has to be in the type, since 'coequalize' builds exactly
-- such a quotient out of objects that are sheaves.
--
-- A 'Subobject' table is still not enough on its own: what is asked is that it cut out a
-- /subsheaf/, as the tables of 'equalize' and the pullbacks do. That much stays a precondition, of
-- the same shape as the two instances above and failing the same loud way -- a glued element
-- outside every fibre is what 'toIndex' reports.
instance (Sheaf t p) => Sheaf t (Reindex Subobject p fs) where
  glue c m = Reindex (glue @t c \l -> case m l of Reindex x -> x)

-- | Whether a predicate on @p@\'s elements picks out a /subprofunctor/: the elements it keeps must
-- be closed under the action, since @'Reindex'@ inherits its 'dimap' from @p@ and so can only carve
-- out a set that is.
--
-- @'dimap' l r@ is @'lmap' l . 'rmap' r@, so closure under the two whiskerings separately is closure
-- under the action: two walks over three objects rather than one over four.
closedUnder
  :: forall {j} {k} (p :: j +-> k)
   . (Finitary p, FiniteCat j, FiniteCat k)
  => (forall a b. (Ob a, Ob b) => p a b -> P.Bool)
  -> P.Bool
closedUnder keep =
  P.and
    ( foreachOb @k \ @a -> foreachOb @j \ @b ->
        let kept = [z | z <- elements @p @a @b, keep z]
        in foreachOb @k @P.Bool (\ @c -> [keep (lmap g z) | g <- elements @(Hom k) @c @a, z <- kept])
             P.++ foreachOb @j @P.Bool (\ @d -> [keep (rmap h z) | h <- elements @(Hom j) @b @d, z <- kept])
    )

-- | Carve a subprofunctor out of @p@, the caller choosing which elements to keep, and receiving the
-- new object\'s inclusion. This is what 'equalize' does with the elements two transformations agree
-- on, exposed so that a caller can pick out a subobject of its own: it is how a value -- a graph read
-- off a file, say -- becomes an object of @'FINITARY' j k@, as a subobject of a big enough ambient
-- one. The failure continuation is taken when the kept set is not 'closedUnder' the action, and so
-- is no subobject.
withSubobject
  :: forall {j} {k} (p :: j +-> k) r
   . (Finitary p, FiniteCat j, FiniteCat k)
  => (forall a b. (Ob a, Ob b) => p a b -> P.Bool)
  -> (forall q. (Finitary q) => FIN q ~> FIN p -> r)
  -> r
  -> r
withSubobject keep ok notClosed =
  if closedUnder @p keep
    then buildTable @j @k (\ @a @b -> [[toIndex x] | x <- elements @p @a @b, keep x]) \ @fs ->
      ok @(Reindex Subobject p fs) (Sub (Prof \(Reindex x) -> x))
    else notClosed

-- * Finitary profunctors presented by their tables

-- | Both tables of a 'Tabulated' profunctor over the objects of @j@ and @k@.
type KnownTables :: Type -> Type -> [[[[Nat]]]] -> [[[[Nat]]]] -> Constraint
type KnownTables j k lm rm = (KnownTable (Objects j) (Objects k) lm, KnownTable (Objects j) (Objects k) rm)

-- | A finitary profunctor given by nothing but its tables: at each pair of objects, for each arrow
-- into @a@ and each arrow out of @b@, the function the arrow induces on element indices. A value is
-- its index, and 'dimap' is two lookups.
--
-- Where 'Reindex' is a /view/ of a profunctor it keeps underneath -- built for free, delegating to
-- @p@ on every use, inheriting @p@'s instances -- this is the /skeleton/: 'withTabulated' pays one
-- full enumeration to build it and nothing is paid afterwards, but nothing is inherited either, which
-- is why the 'Sheaf' instance below has to search. Every finitary profunctor tabulates, so a costly
-- one -- 'Proarrow.Category.Enriched.Finitary.Sheaf.Sheafify' re-runs its whole enumeration on every
-- 'toIndex', since a 'Finitary' instance cannot memoise -- can be replaced by its tables where it is
-- used often.
--
-- The @lm@ table has, at @(a, b)@, one row per arrow @g :: c '~>' a@ in 'arrowSlot' order, listing
-- @'toIndex' ('lmap' g x)@ for each element @x@ in index order; @rm@ has one row per @h :: b '~>' d@
-- in 'coarrowSlot' order for 'rmap'. A row's length is the size at @(a, b)@, so no third table.
--
-- The @t@ parameter is the coverage the presentation has been /checked/ to be a sheaf for. The
-- tables cannot say whether it is one -- the 'Sheaf' instance below can only assert it -- so the
-- assertion is left to the two builders, which are the only things that should ever apply a tag.
-- 'withTabulated' asserts nothing, taking 'Trivial', which has no covers;
-- 'Proarrow.Category.Enriched.Finitary.Sheaf.withTabulatedSheaf' decides the condition by
-- enumeration first.
type Tabulated :: forall {j} {k}. Type -> [[[[Nat]]]] -> [[[[Nat]]]] -> j +-> k
data Tabulated t lm rm a b where
  Tabulated :: (Ob a, Ob b) => Natural -> Tabulated t lm rm a b

-- | Where an arrow sits among all the arrows into its target: by source object first, then by the
-- arrow's own index. The row order of a 'Tabulated' @lm@ table.
arrowSlot :: forall {k} (c :: k) a. (FiniteCat k, Ob c, Ob a) => c ~> a -> Natural
arrowSlot g = P.sum (foreachOb @k \ @c' -> [size @(Hom k) @c' @a | objIndex @c' P.< objIndex @c]) P.+ toIndex g

-- | Where an arrow sits among all the arrows out of its source: the row order of an @rm@ table.
coarrowSlot :: forall {j} (b :: j) d. (FiniteCat j, Ob b, Ob d) => b ~> d -> Natural
coarrowSlot h = P.sum (foreachOb @j \ @d' -> [size @(Hom j) @b @d' | objIndex @d' P.< objIndex @d]) P.+ toIndex h

-- | 'lmap' reads the arrow's row in the @lm@ cell at the value's index; 'rmap' then reads the @rm@
-- cell at the new source object.
instance (FiniteCat j, FiniteCat k, KnownTables j k lm rm) => Profunctor (Tabulated t lm rm :: j +-> k) where
  dimap @c @a @b @_ l r (Tabulated i) =
    l // r // Tabulated (look (cellVal @rm @c @b) (coarrowSlot r) (look (cellVal @lm @a @b) (arrowSlot l) i))
    where
      look cell slot = genericIndex (genericIndex cell slot)
  r \\ Tabulated{} = r

-- | The numbering is the value: 'size' is a row's length and the rest is the identity -- but for
-- the range check, which an index that /is/ the value has nowhere else to fail: stored unchecked it
-- would surface much later, as 'genericIndex' running off a row inside 'dimap'.
instance (FiniteCat j, FiniteCat k, KnownTables j k lm rm) => Finitary (Tabulated t lm rm :: j +-> k) where
  size @a @b = case cellVal @lm @a @b of
    row : _ -> genericLength row
    [] -> P.error "Tabulated: empty cell"
  toIndex (Tabulated i) = i
  fromIndex @a @b i
    | i P.< size @(Tabulated t lm rm) @a @b = Tabulated i
    | P.otherwise = P.error "Tabulated: index out of range"

-- | The two tables of @p@, reified, with nothing said about what they present. The enumeration --
-- every element, every arrow, one 'toIndex' per pair -- is paid here and never again. The two
-- builders differ only in the tag they hand the tables to, so the enumeration is written once,
-- here; the other builder is 'Proarrow.Category.Enriched.Finitary.Sheaf.withTabulatedSheaf', which
-- lives over there because deciding the sheaf condition needs what is built on this module.
withTables
  :: forall {j} {k} (p :: j +-> k) r
   . (Finitary p, FiniteCat j, FiniteCat k)
  => (forall lm rm. (KnownTables j k lm rm) => r)
  -> r
withTables k =
  buildTable @j @k
    ( \ @a @b -> let xs = elements @p @a @b in foreachOb @k \ @c -> [P.map (toIndex . lmap g) xs | g <- elements @(Hom k) @c @a]
    )
    \ @lm ->
      buildTable @j @k
        ( \ @a @b -> let xs = elements @p @a @b in foreachOb @j \ @d -> [P.map (toIndex . rmap h) xs | h <- elements @(Hom j) @b @d]
        )
        \ @rm -> k @lm @rm

-- | An element of @p@ as the index that stands for it in a presentation of @p@.
toTabulated :: forall {j} {k} t lm rm (p :: j +-> k). (Finitary p) => p :~> Tabulated t lm rm
toTabulated x = Tabulated (toIndex x) \\ x

-- | An index in a presentation of @p@ as the element of @p@ it stands for.
fromTabulated :: forall {j} {k} t lm rm (p :: j +-> k). (Finitary p) => Tabulated t lm rm :~> p
fromTabulated (Tabulated i) = fromIndex i

-- | Present a finitary profunctor by its tables, once, and hand on the presentation with the
-- isomorphism both ways.
--
-- The continuation receives the presentation as a named profunctor @tab@ of the right kind, equal to
-- @'Tabulated' 'Trivial' lm rm@: the tables alone do not fix @j@ and @k@, so a caller who wrote that
-- out would have to annotate every mention. Bind it as @\\ \@tab toTab fromTab -> ...@.
--
-- The presentation is a sheaf for 'Trivial' and says nothing about any other coverage. To present
-- a sheaf /as/ one, use 'Proarrow.Category.Enriched.Finitary.Sheaf.withTabulatedSheaf'.
withTabulated
  :: forall {j} {k} (p :: j +-> k) r
   . (Finitary p, FiniteCat j, FiniteCat k)
  => ( forall {lm} {rm} (tab :: j +-> k)
        . (tab ~ Tabulated Trivial lm rm, KnownTables j k lm rm)
       => (p :~> tab)
       -> (tab :~> p)
       -> r
     )
  -> r
withTabulated k = withTables @p \ @lm @rm -> k @(Tabulated Trivial lm rm) toTabulated fromTabulated

-- | Glue by search: the element whose restrictions along the legs are the family. This is
-- 'Proarrow.Category.Enriched.Finitary.Sheaf.isSheaf'\'s bijection read backwards, and it is what
-- makes a sheaf without 'glue' of its own -- a 'Tabulated' one, or a subsheaf cut out of a
-- profunctor that is no sheaf, like the closed sieves -- an instance. Lawful exactly when @p@ is a
-- sheaf, which is then a fact about where @p@ came from; 'isSheaf' decides it.
--
-- A bijection has two ways to fail and both are caught here, since a search that answers at all
-- answers silently: no element restricting to the family, and more than one. The second is not a
-- corner case -- over a cover with no legs every element matches, so it is the whole of what being
-- /separated/ asks at that cover, and without the check an unseparated profunctor would glue to
-- whichever element came first.
glueBySearch
  :: forall t {j} {k} (p :: j +-> k) (a :: k) c (b :: j)
   . (Site t k, Finitary p, Ob a, Ob b)
  => Cover t k a c
  -> (forall x. Leg t k a c x -> p x b)
  -> p a b
glueBySearch c m = case P.filter restrictsToTheFamily (elements @p @a @b) of
  [x] -> x
  [] -> P.error "glue: no element restricts to the family -- not a sheaf"
  _ -> P.error "glue: more than one element restricts to the family -- not a sheaf"
  where
    restrictsToTheFamily x = P.all (\(SomeLeg l, i) -> (toIndex (lmap (legArrow l) x) == i) \\ legArrow l) family
    family :: [(SomeLeg t k a c, Natural)]
    family = [(SomeLeg l, toIndex (m l) \\ legArrow l) | SomeLeg l <- legs c]

-- | A tabulated profunctor glues by search, since it knows nothing of the profunctor it presents.
-- Only for the coverage its tag names: the tag is the whole of the evidence that the search will
-- find its element, so a presentation may be used as a sheaf for the coverage it was checked
-- against and for no other. At 'Trivial', which 'withTabulated' applies and which has no covers,
-- the instance is vacuous and 'glueBySearch' is unreachable.
instance (Site t k, FiniteCat j, FiniteCat k, KnownTables j k lm rm) => Sheaf t (Tabulated t lm rm :: j +-> k) where
  glue = glueBySearch @t

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
  equalize (Sub (Prof f)) (Sub (Prof g)) k = equalizeNat f g \incl -> k (Sub (Prof incl))
  factorEqualizer (Sub (Prof incl)) (Sub (Prof h)) = Sub (Prof (factorThroughEqualizer incl h))

-- | The equalizer of two natural transformations: the source retabulated along the points where
-- they agree, handed on with its inclusion. 'FINITARY' and its subcategories of sheaves equalize
-- alike; only the wrapper around the result differs, so the construction lives here once.
equalizeNat
  :: forall {j} {k} (p :: j +-> k) q r
   . (Finitary p, Finitary q, Enumerable j, Enumerable k)
  => (p :~> q)
  -> (p :~> q)
  -> (forall fs. (KnownTable (Objects j) (Objects k) fs) => (Reindex Subobject p fs :~> p) -> r)
  -> r
equalizeNat f g k =
  buildTable @j @k
    ( \ @a @b ->
        let toIndexP = toIndex @p @a @b; toIndexQ = toIndex @q @a @b
        in [[toIndexP x] | x <- elements @p @a @b, toIndexQ (f x) == toIndexQ (g x)]
    )
    \ @fs -> k @fs \(Reindex x) -> x

-- | Factor through an equalizer's inclusion, by 'preimage': the arrow must land in the image.
factorThroughEqualizer
  :: forall {j} {k} (e :: j +-> k) x e'
   . (Finitary e, Finitary x, Profunctor e')
  => (e :~> x)
  -> (e' :~> x)
  -> e' :~> e
factorThroughEqualizer incl h y = preimage "factorEqualizer: h's image must lie within incl's image" incl (h y) \\ y

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
      \ @fs -> k (Sub (Prof @q @(Reindex Quotient q fs) Reindex))
  factorCoequalizer (Sub (Prof @_ @c proj)) (Sub (Prof @_ @c' h)) =
    Sub (Prof @c @c' \y -> h (preimage "factorCoequalizer: proj must be onto" proj y) \\ y)

-- * Pullbacks, pushouts and images

-- | Pullbacks are equalizers of products, and pushouts coequalizers of coproducts, all of which
-- finitary profunctors have.
instance (Enumerable j, Enumerable k) => HasPullbacks (FINITARY j k)

instance (Enumerable j, Enumerable k) => HasPushouts (FINITARY j k)

-- | The image of a natural transformation is the equalizer of its cokernel pair.
instance (Enumerable j, Enumerable k) => HasEpiMonoFactorization (FINITARY j k)

-- * Natural transformations, enumerated

-- | Enumerate a set of families by brute force: every way of choosing a value at each point of the
-- domain, kept when it satisfies every condition. A condition is checked as soon as both of its
-- points have been chosen, so a violation prunes the whole subtree of completions rather than
-- rejecting each of them in turn -- which is what keeps the candidate space from being the full
-- product. Families come out in the same order as @'P.sequence' choices@ would give them: the
-- earliest point varies slowest.
familiesSatisfying :: [[v]] -> [(P.Int, P.Int, v -> v -> P.Bool)] -> [[v]]
familiesSatisfying choices laws = go 0 [] choices
  where
    -- a condition can first be tested at the later of its two points
    byDepth = IM.fromListWith (P.++) [(P.max src tgt, [(src, tgt, rel)]) | (src, tgt, rel) <- laws]
    go _ chosen [] = [P.reverse chosen]
    go i chosen (cs : rest) =
      [ row
      | v <- cs
      , let chosen' = v : chosen
      , let at n = chosen' P.!! (i P.- n) -- @chosen'@ holds points @0..i@ in reverse
      , P.all (\(src, tgt, rel) -> rel (at src) (at tgt)) (IM.findWithDefault [] i byDepth)
      , row <- go (i P.+ 1) chosen' rest
      ]

-- | Which of the enumerated families a tabulated one is.
familyIndex :: (P.Eq v) => P.String -> [[v]] -> [v] -> Natural
familyIndex msg fams row = case elemIndex row fams of
  Just i -> P.fromIntegral i
  Nothing -> P.error msg

-- | One point of the domain of the end @∫ Set(p c d, q c d)@ whose elements are the natural
-- transformations @p -> q@: an object pair and an element of @p@ there. Every end below is one of
-- these: the internal hom only changes the weight @p@, and the subobject classifier also changes
-- what the conditions are read as. So this is the single enumeration the topos is built on.
type NatKey = (Natural, Natural, Natural)

-- | Visit every point of that domain, in one fixed order.
natDomain
  :: forall {j} {k} (p :: j +-> k) r
   . (Finitary p, FiniteCat j, FiniteCat k)
  => (forall a b. (Ob a, Ob b) => p a b -> r)
  -> [r]
natDomain f = foreachOb @k \ @a -> foreachOb @j \ @b -> P.map f (elements @p @a @b)

natKey
  :: forall {j} {k} (a :: k) (b :: j) (p :: j +-> k). (FiniteCat j, FiniteCat k, Finitary p, Ob a, Ob b) => p a b -> NatKey
natKey x = (objIndex @a, objIndex @b, toIndex x)

-- | Where each point of the domain sits in a tabulated family. This is the same for every family
-- over a given weight, so bind it once outside a loop over them.
natPositions
  :: forall {j} {k} (p :: j +-> k). (Finitary p, FiniteCat j, FiniteCat k) => M.Map NatKey P.Int
natPositions = natPositionsBy @p natKey

-- | 'natPositions' with the key chosen by the caller, for a weight whose points are addressed by
-- another object's keys -- a subobject carved out by 'withSubobject', whose inclusion says which
-- point of the ambient object each of its own points is.
natPositionsBy
  :: forall {j} {k} (p :: j +-> k)
   . (Finitary p, FiniteCat j, FiniteCat k)
  => (forall a b. (Ob a, Ob b) => p a b -> NatKey)
  -> M.Map NatKey P.Int
natPositionsBy key = M.fromList (P.zip (natDomain @p @NatKey key) [0 ..])

-- | Read a tabulated family back as a function on the points, given those positions.
atNatKey :: M.Map NatKey P.Int -> [v] -> NatKey -> v
atNatKey pos row k = row P.!! (pos M.! k)

-- | Every natural transformation @p -> q@, as its list of @q@-indices in 'natDomain' order.
-- Naturality is the only condition: the value at @x@ and the value at @'dimap' g h x@ must agree
-- after transport.
natElements
  :: forall {j} {k} (p :: j +-> k) (q :: j +-> k)
   . (Finitary p, Finitary q, FiniteCat j, FiniteCat k)
  => [[Natural]]
natElements =
  familiesSatisfying
    -- the same choice list at every point over one object pair, so @q@\'s size is asked once per pair
    (foreachOb @k \ @a -> foreachOb @j \ @b -> genericReplicate (size @p @a @b) (indices (size @q @a @b)))
    (natConditions @p @q \tr i j -> j == genericIndex tr i)

-- | The conditions as positions in a tabulated family, with @q@\'s transport handed to the
-- relation. Only the internal hom reads that transport; the sieves below ignore it, and pass
-- 'TerminalProfunctor' for @q@ so that computing it costs nothing.
natConditions
  :: forall {j} {k} (p :: j +-> k) (q :: j +-> k) v
   . (Finitary p, Finitary q, FiniteCat j, FiniteCat k)
  => ([Natural] -> v -> v -> P.Bool)
  -> [(P.Int, P.Int, v -> v -> P.Bool)]
natConditions rel = [(at src, at tgt, rel tr) | (src, tgt, tr) <- natLaws @p @q]
  where
    at = (natPositions @p M.!)

-- | The naturality conditions on a transformation. As in 'closedUnder', @'dimap' g h@ is
-- @'lmap' g . 'rmap' h@, so commuting with the two whiskerings separately is commuting with the
-- action: two walks over three objects rather than one over four, and the transport table depends
-- on the arrow alone rather than on each element.
natLaws
  :: forall {j} {k} (p :: j +-> k) (q :: j +-> k)
   . (Finitary p, Finitary q, FiniteCat j, FiniteCat k)
  => [(NatKey, NatKey, [Natural])]
natLaws =
  foreachOb @k \ @a -> foreachOb @j \ @b ->
    let xs = elements @p @a @b; qs = elements @q @a @b
    in foreachOb @k @(NatKey, NatKey, [Natural])
         ( \ @c -> [(natKey x, natKey (lmap g x), tr) | g <- elements @(Hom k) @c @a, let tr = P.map (toIndex . lmap g) qs, x <- xs]
         )
         P.++ foreachOb @j @(NatKey, NatKey, [Natural])
           ( \ @d -> [(natKey x, natKey (rmap h x), tr) | h <- elements @(Hom j) @b @d, let tr = P.map (toIndex . rmap h) qs, x <- xs]
           )

-- | A natural transformation as its table of @q@-indices, in 'natDomain' order. That is everything
-- there is to see of one, so it serves for both comparing and showing.
natTable
  :: forall {j} {k} (p :: j +-> k) (q :: j +-> k)
   . (Finitary p, Finitary q, FiniteCat j, FiniteCat k)
  => (p :~> q)
  -> [Natural]
natTable f = natDomain @p (toIndex P.. f)

-- | Which of the natural transformations @p -> q@ a given one is: 'familyIndex' of its 'natTable' in
-- 'natElements'. The enumeration is bound before the transformation arrives, so a partial
-- application shares it across a hom-set; every 'toIndex' that numbers transformations is this one.
natIndex
  :: forall {j} {k} (p :: j +-> k) (q :: j +-> k)
   . (Finitary p, Finitary q, FiniteCat j, FiniteCat k)
  => P.String
  -> (p :~> q)
  -> Natural
natIndex msg = \f -> familyIndex msg es (natTable @p @q f)
  where
    es = natElements @p @q

-- | Every natural transformation @p -> q@, as an arrow of @j '+->' k@. This is what makes the
-- category of finitary profunctors -- and each of its full subcategories -- testable: its hom-sets
-- are enumerable, so a generator can pick from them, where in general a natural transformation is
-- not something one can generate.
natTransformations
  :: forall {j} {k} (p :: j +-> k) (q :: j +-> k)
   . (Finitary p, Finitary q, FiniteCat j, FiniteCat k)
  => [p ~> q]
natTransformations = let pos = natPositions @p in P.map (natAt @p @q pos) (natElements @p @q)

-- | A tabulated transformation, as an arrow of @j '+->' k@.
natAt
  :: forall {j} {k} (p :: j +-> k) (q :: j +-> k)
   . (Finitary p, Finitary q, FiniteCat j, FiniteCat k)
  => M.Map NatKey P.Int
  -> [Natural]
  -> p ~> q
natAt pos row = Prof \x -> x // fromIndex @q (atNatKey pos row (natKey x))

-- | @'Finitary' p@ as a class with a single instance, so that a quantified constraint can ask for
-- it without 'Finitary' being the head; 'subFinitary' hands it back as an ordinary given. The
-- instance below says what this is for. 'Proarrow.Optic.Sub' is the same device for flavors, and
-- documents the GHC restriction behind it at more length -- including why neither of them carries
-- the constraint it wraps as a superclass.
type SubFinitary :: forall {j} {k}. (j +-> k) -> Constraint
class SubFinitary p where
  subFinitary :: ((Finitary p) => r) -> r

instance (Finitary p) => SubFinitary p where
  subFinitary r = r

-- | @'FINITARY' j k@ is locally finite: its own hom-profunctor is finitary, by 'natTransformations'.
-- So the numbering above is not just a testing device, it is the skeleton of each hom-set, and the
-- 'Finitary' laws apply to it like to any other. (It is not a 'FiniteCat' -- there are unboundedly
-- many finitary profunctors -- which is exactly the difference between finite and locally finite.)
--
-- Every full subcategory of it is locally finite the same way, whatever predicate cuts it out --
-- @'FINITARY' j k@ itself, or the sheaves of "Proarrow.Category.Enriched.Finitary.Sheaf" -- so long
-- as that predicate implies 'Finitary'. Asking for it as the bare @forall p. ob p => 'Finitary' p@
-- would cover the first and not the second: GHC will not solve the head of a quantified constraint
-- from a superclass of its premise unless the superclass is strictly smaller than the head, and
-- @'Finitary' p@ out of @('Finitary' :&&: 'Sheaf' t) p@ is not smaller. Behind 'SubFinitary' the
-- head is a class of its own and @'Finitary' p@ is an ordinary wanted, solved from the premise\'s
-- superclasses as usual.
instance
  (FiniteCat j, FiniteCat k, forall p. (ob p) => SubFinitary p)
  => Finitary (Sub Prof :: CAT (SUBCAT (ob :: OB (j +-> k))))
  where
  size @f @g = subFinitary @(UN SUB f) $ subFinitary @(UN SUB g) $ genericLength (natElements @(UN SUB f) @(UN SUB g))
  toIndex @f @g =
    subFinitary @(UN SUB f) $
      subFinitary @(UN SUB g) $
        -- bound before the argument lambda, so a partial application shares the enumeration
        let ix = natIndex @(UN SUB f) @(UN SUB g) "toIndex: the transformation is not natural"
        in \(Sub (Prof n)) -> ix n
  fromIndex @f @g i =
    subFinitary @(UN SUB f) $
      subFinitary @(UN SUB g) $
        Sub (natAt @(UN SUB f) @(UN SUB g) (natPositions @(UN SUB f)) (genericIndex (natElements @(UN SUB f) @(UN SUB g)) i))
  elements @f @g = subFinitary @(UN SUB f) $ subFinitary @(UN SUB g) $ P.map Sub (natTransformations @(UN SUB f) @(UN SUB g))

-- | What the internal hom at @a@\/@b@ is a set of natural transformations /out of/. An element of
-- it over @c@\/@d@ is an arrow into @a@, an arrow out of @b@ and an element of @p@ -- exactly the
-- three arguments an 'Exp' takes.
type ExpWeight :: forall {j} {k}. (j +-> k) -> k -> j -> j +-> k
type ExpWeight p a b = Yo a (OP b) :*: p

-- | The internal hom of finitary profunctors is finitary: its elements are the natural
-- transformations out of 'ExpWeight', enumerated. Nothing here is a formula in the sizes of @p@ and
-- @q@ -- the count depends on how the arrows of @j@ and @k@ compose -- which is why 'size' is a
-- value and not a type family.
instance (Finitary p, Finitary q, FiniteCat j, FiniteCat k) => Finitary (p :~>: q :: j +-> k) where
  size @a @b = genericLength (natElements @(ExpWeight p a b) @q)

  toIndex @a @b = \(Exp f) -> ix \(Yo ca bd :*: x) -> f ca bd x
    where
      ix = natIndex @(ExpWeight p a b) @q "toIndex: the family is not natural"
  fromIndex @a @b i = expAt @p @q (natPositions @(ExpWeight p a b)) (genericIndex (natElements @(ExpWeight p a b) @q) i)
  elements @a @b =
    let pos = natPositions @(ExpWeight p a b) in P.map (expAt @p @q pos) (natElements @(ExpWeight p a b) @q)

-- | A tabulated family as an element of the internal hom.
expAt
  :: forall {j} {k} (p :: j +-> k) (q :: j +-> k) (a :: k) (b :: j)
   . (Finitary p, Finitary q, FiniteCat j, FiniteCat k, Ob a, Ob b)
  => M.Map NatKey P.Int
  -> [Natural]
  -> (p :~>: q) a b
expAt pos row = Exp \ca bd x -> ca // bd // fromIndex @q (atNatKey pos row (natKey (Yo ca bd :*: x)))

-- | Finitary profunctors are cartesian closed. The 'PROD' wrapper is what makes the tensor the
-- product rather than Day convolution, exactly as it does for @j '+->' k@ itself.
instance (FiniteCat j, FiniteCat k) => Closed (PROD (FINITARY j k)) where
  type p ~~> q = PR (SUB (UN SUB (UN PR p) :~>: UN SUB (UN PR q)))
  withObExp r = r
  curry (Prod (Sub (Prof n))) = Prod (Sub (Prof \p -> p // Exp \ca bd q -> n (dimap ca bd p :*: q)))
  apply = Prod (Sub (Prof \(Exp f :*: q) -> f id id q \\ q))
  Prod (Sub (Prof m)) ^^^ Prod (Sub (Prof n)) = Prod (Sub (Prof \(Exp f) -> Exp \ca bd p -> m (f ca bd (n p))))

-- * The subobject classifier

-- | Every sieve at @a@\/@b@, as the points of @'Yo' a ('OP' b)@ it contains, in 'natDomain' order:
-- all subsets, kept when closed. This is the same end again, at the weight @'Yo' a ('OP' b)@ and
-- valued in booleans, with the naturality conditions read as implications rather than equations.
sieveElements :: forall {j} {k} (a :: k) (b :: j). (FiniteCat j, FiniteCat k, Ob a, Ob b) => [[P.Bool]]
sieveElements =
  familiesSatisfying
    (natDomain @(Yo a (OP b)) (P.const [P.False, P.True]))
    (natConditions @(Yo a (OP b)) @TerminalProfunctor \_ s t -> P.not s P.|| t)

-- | A sieve as the tabulation of its membership, in 'natDomain' order -- the inverse of 'sieveAt'.
sieveTable :: forall {j} {k} (a :: k) (b :: j). (FiniteCat j, FiniteCat k) => Sieve a b -> [P.Bool]
sieveTable (Sieve s) = natDomain @(Yo a (OP b)) \(Yo ca bd) -> s ca bd

instance (FiniteCat j, FiniteCat k) => Finitary (Sieve :: j +-> k) where
  size @a @b = genericLength (sieveElements @a @b)
  toIndex @a @b = familyIndex "toIndex: not a sieve" (sieveElements @a @b) . sieveTable
  fromIndex @a @b i = sieveAt (natPositions @(Yo a (OP b))) (genericIndex (sieveElements @a @b) i)
  elements @a @b = let pos = natPositions @(Yo a (OP b)) in P.map (sieveAt pos) (sieveElements @a @b)

-- | A tabulated sieve as a sieve.
sieveAt
  :: forall {j} {k} (a :: k) (b :: j)
   . (FiniteCat j, FiniteCat k, Ob a, Ob b)
  => M.Map NatKey P.Int
  -> [P.Bool]
  -> Sieve a b
sieveAt pos row = Sieve \ca bd -> ca // bd // atNatKey pos row (natKey (Yo ca bd))

-- | The subobject classifier is the profunctor of sieves, and an arrow classifies its graph: the
-- sieve of all the ways an element of @p@ and one of @q@ can be carried to a matching pair.
instance (FiniteCat j, FiniteCat k) => HasSubobjectClassifier (PROD (FINITARY j k)) where
  type Omega = PR (SUB Sieve)
  true = Prod (Sub (Prof \TerminalProfunctor -> maximalSieve))
  classifyGraph (Prod (Sub (Prof @_ @q f))) =
    Prod (Sub (Prof \(x :*: y) -> x // Sieve \g h -> g // h // toIndex @q (f (dimap g h x)) == toIndex (dimap g h y)))

-- | Finitary profunctors between finite categories form an elementary topos: finite limits and
-- colimits, cartesian closed, a subobject classifier, and image factorization.
instance (FiniteCat j, FiniteCat k) => ElementaryTopos (PROD (FINITARY j k))
