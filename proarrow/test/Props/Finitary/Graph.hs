{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The same topos laws as "Props.Finitary", but over a category with something going on in both
-- variances: @'FINITARY' 'GRAPH' 'BOOL'@. A profunctor @'GRAPH' '+->' 'BOOL'@ is a graph for each
-- object of the walking arrow together with a graph homomorphism between them, so this kind is the
-- arrow category of graphs. Being a presheaf category, it is an elementary topos like any other.
module Props.Finitary.Graph (test) where

import Data.List (genericIndex, genericLength)
import Numeric.Natural (Natural)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (.))

import Examples.Graph (GRAPH (..), GraphHom (..))
import Proarrow.Category.Enriched.Finitary (Finitary (..), factorThrough, sizes)
import Proarrow.Category.Enriched.Finitary.Topos (FIN, FINITARY)
import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..), IsBool (..))
import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Category.Instance.Prof (Prof)
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub)
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), obj, (//), type (+->))
import Proarrow.Limit.BinaryProduct (PROD (..))
import Proarrow.Profunctor.Instance.Coproduct ((:+:))
import Proarrow.Profunctor.Instance.Exponential ((:~>:))
import Proarrow.Profunctor.Instance.Sieve (Sieve)
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor)
import Proarrow.Profunctor.Instance.Yoneda (Yo)
import Proarrow.Testing
  ( Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , expect
  , genSomeDef
  , optGen
  )
import Proarrow.Testing.Laws
  ( testBinaryCoproducts_
  , testBinaryProducts_
  , testCategory
  , testClosed_
  , testCoequalizers_
  , testEqualizers_
  , testFinitary
  , testInitialObject
  , testPullbacks_
  , testPushouts_
  , testTerminalObject
  )
import Props.Bool ()

-- | The kind of finitary graph homomorphisms. Contravariant in 'BOOL' and covariant in 'GRAPH':
-- @'lmap' 'F2T'@ is the homomorphism itself, carrying the graph at 'TRU' to the graph at 'FLS'.
type GHom = FINITARY GRAPH BOOL

-- * Three graph homomorphisms to test over

-- | The identity on the graph with one edge and two distinct endpoints. Nothing happens in the
-- 'BOOL' direction, and the two incidence maps disagree, so 'Src' and 'Tgt' are distinguishable.
type Same :: GRAPH +-> BOOL
data Same a b where
  SameE :: (IsBool a) => Same a E
  SameS :: (IsBool a) => Same a V
  SameT :: (IsBool a) => Same a V

deriving instance Eq (Same a b)
deriving instance Show (Same a b)

instance Profunctor Same where
  dimap ba dg x =
    ba // case (dg, x) of
      (IdE, SameE) -> SameE
      (IdV, SameS) -> SameS
      (IdV, SameT) -> SameT
      (Src, SameE) -> SameS
      (Tgt, SameE) -> SameT
  r \\ x = case x of SameE -> r; SameS -> r; SameT -> r

-- | The elements over each object, in the order the numbering below uses.
sameElements :: forall a b. (Ob a, Ob b) => [Same a b]
sameElements = case obj @b of
  IdE -> [SameE]
  IdV -> [SameS, SameT]

instance Finitary Same where
  size @a @b = genericLength (sameElements @a @b)
  toIndex SameE = 0
  toIndex SameS = 0
  toIndex SameT = 1
  fromIndex @a @b i = sameElements @a @b `genericIndex` i
  elements = sameElements

-- | The homomorphism that folds that edge into a self-loop: both endpoints go to the one vertex.
-- Non-injective in the 'BOOL' direction, and the loop makes 'Src' and 'Tgt' agree at 'FLS' while
-- they still differ at 'TRU'.
type Fold :: GRAPH +-> BOOL
data Fold a b where
  FoldE :: Fold TRU E
  FoldS :: Fold TRU V
  FoldT :: Fold TRU V
  LoopE :: Fold FLS E
  LoopV :: Fold FLS V

deriving instance Eq (Fold a b)
deriving instance Show (Fold a b)

-- | The 'FLS' layer has one element over each object, so an element there is determined by which
-- object the arrow lands on. So the action on it is forced.
atLoop :: GraphHom b d -> Fold FLS d
atLoop IdE = LoopE
atLoop IdV = LoopV
atLoop Src = LoopV
atLoop Tgt = LoopV

instance Profunctor Fold where
  dimap Fls dg _ = atLoop dg
  dimap F2T dg _ = atLoop dg
  dimap Tru IdE FoldE = FoldE
  dimap Tru IdV x = x
  dimap Tru Src FoldE = FoldS
  dimap Tru Tgt FoldE = FoldT
  r \\ x = case x of FoldE -> r; FoldS -> r; FoldT -> r; LoopE -> r; LoopV -> r

foldElements :: forall a b. (Ob a, Ob b) => [Fold a b]
foldElements = case (boolId @a, obj @b) of
  (Tru, IdE) -> [FoldE]
  (Tru, IdV) -> [FoldS, FoldT]
  (Fls, IdE) -> [LoopE]
  (Fls, IdV) -> [LoopV]

instance Finitary Fold where
  size @a @b = genericLength (foldElements @a @b)
  toIndex FoldE = 0
  toIndex FoldS = 0
  toIndex FoldT = 1
  toIndex LoopE = 0
  toIndex LoopV = 0
  fromIndex @a @b i = foldElements @a @b `genericIndex` i
  elements = foldElements

instance (Ob a, Ob b) => TestingEqShow (Same a b)
instance (Ob a, Ob b) => TestingEqShow (Fold a b)

-- | Spelled out instead of taken from 'elements', so that 'testFinitary' compares the numbering
-- against something independent of it, as in "Props.Finitary".
instance (Ob a, Ob b) => TestableType (Same a b) where
  gen = case obj @b of
    IdE -> optGen [SameE]
    IdV -> optGen [SameS, SameT]

instance (Ob a, Ob b) => TestableType (Fold a b) where
  gen = case (boolId @a, obj @b) of
    (Tru, IdE) -> optGen [FoldE]
    (Tru, IdV) -> optGen [FoldS, FoldT]
    (Fls, IdE) -> optGen [LoopE]
    (Fls, IdV) -> optGen [LoopV]

-- | The identity on the graph with one vertex and no edges. Empty over 'E', so hom-sets out of it
-- are the ones that go empty, and the properties discard instead of failing.
type Dot :: GRAPH +-> BOOL
data Dot a b where
  DotV :: (IsBool a) => Dot a V

instance Profunctor Dot where
  -- 'DotV' first: only then does GHC see that @b@ is 'V', so that 'IdV' is the only arrow out of it
  dimap ba dg DotV = case dg of IdV -> ba // DotV
  r \\ DotV = r

dotElements :: forall a b. (Ob a, Ob b) => [Dot a b]
dotElements = case obj @b of
  IdE -> []
  IdV -> [DotV]

instance Finitary Dot where
  size @a @b = genericLength (dotElements @a @b)
  toIndex DotV = 0
  fromIndex @a @b i = dotElements @a @b `genericIndex` i
  elements = dotElements

-- * The arrow category of graphs, as a testable kind

instance TestableProfunctor (Sub Prof :: CAT GHom)

-- | As in "Props.Finitary": objects come from a fixed palette, and are displayed by their table of
-- sizes, here the four numbers @[FLS\/E, FLS\/V, TRU\/E, TRU\/V]@.
instance Testable GHom where
  showOb @(SUB p) = show (sizes @p)

  -- 'Same' twice over gives a palette object of size 2 at every point. Without one, nine of the
  -- ten non-empty hom-sets are singletons, where an equation between parallel arrows holds by
  -- type-correctness alone and the run asserts nothing. Built from the library's ':+:', whose
  -- 'Finitary' instance supplies the numbering.
  genSome = genSomeDef @'[FIN Same, FIN Fold, FIN Dot, FIN TerminalProfunctor, FIN (Same :+: Same)]

  -- The internal hom enumerates candidate tables by brute force, so it cannot afford the object
  -- above: @sizes \@(Same :+: Same)@ is @[2,4,2,4]@, but the hom /into/ it is @[1024,256,1024,256]@,
  -- and enumerating one such hom-set measured 13.6s and 36.6GB. 'testClosed' draws from
  -- 'genSomeSmall', so the two coexist.
  genSomeSmall = genSomeDef @'[FIN Same, FIN Fold, FIN Dot, FIN TerminalProfunctor]

-- | The sizes of @1 ~~> p@ and of @p@ over one object, which Yoneda says must agree.
yoneda :: forall (p :: GRAPH +-> BOOL). (Finitary p) => [(Natural, Natural)]
yoneda = zip (sizes @(TerminalProfunctor :~>: p)) (sizes @p)

test :: TestTree
test =
  testGroup
    "Finitary.Graph"
    [ testCategory @GHom
    , testTerminalObject @GHom
    , testInitialObject @GHom
    , testBinaryProducts_ @GHom
    , testBinaryCoproducts_ @GHom
    , testClosed_ @(PROD GHom)
    , testEqualizers_ @GHom
    , testCoequalizers_ @GHom
    , testPullbacks_ @GHom
    , testPushouts_ @GHom
    , -- 'GRAPH' is the only non-thin finite category here, so it is the only place
      -- 'factorThrough' has anything to decide. In a thin one @f . h@ and @g@ are both the unique
      -- arrow of their hom-set, so the check succeeds whenever the hom-set is non-empty. The sheaf
      -- sites are both thin, so @Props.Sheaf@ cannot exercise this.
      testProperty "factorThrough decides, where there is a choice of arrow" $ do
        expect "Src factors through itself" (Just IdE) (factorThrough Src Src)
        expect "Tgt does not factor through Src" Nothing (factorThrough Tgt Src)
        expect "Src factors through IdV" (Just Src) (factorThrough Src IdV)
    , testFinitary @Same "Same"
    , testFinitary @Fold "Fold"
    , -- the palette object added above, so its numbering is law-checked and not merely used
      testFinitary @(Same :+: Same) "Same + Same"
    , -- as in "Props.Finitary": this checks the table round trip, the counts below check that the
      -- enumeration is complete
      testFinitary @(Sub Prof :: CAT GHom) "GHom"
    , testProperty "the hom-sets have the sizes a hand count gives them" $ do
        -- a lone vertex picks an endpoint of the edge, and the same one in both layers
        expect "Dot -> Same" 2 (size @(Sub Prof) @(FIN Dot) @(FIN Same))
        expect "Dot -> Fold" 2 (size @(Sub Prof) @(FIN Dot) @(FIN Fold))
        -- the edge graph has one endomorphism and one map onto the loop, both forced by 'Src'
        -- and 'Tgt' having to be preserved
        expect "Same -> Same" 1 (size @(Sub Prof) @(FIN Same) @(FIN Same))
        expect "Same -> Fold" 1 (size @(Sub Prof) @(FIN Same) @(FIN Fold))
        -- backwards there is nothing: a loop would need its one vertex to be both endpoints
        expect "Fold -> Same" 0 (size @(Sub Prof) @(FIN Fold) @(FIN Same))
        -- and a graph with no edges cannot receive one
        expect "Same -> Dot" 0 (size @(Sub Prof) @(FIN Same) @(FIN Dot))
        -- the edge graph has no global sections, for the same reason the loop has no map into it
        expect "1 -> Same" 0 (size @(Sub Prof) @(FIN TerminalProfunctor) @(FIN Same))
    , testProperty "the exponential by the terminal object is the profunctor itself" $ do
        expect "Same" [(1, 1), (2, 2), (1, 1), (2, 2)] (yoneda @Same)
        expect "Fold" [(1, 1), (1, 1), (1, 1), (2, 2)] (yoneda @Fold)
        expect "Dot" [(0, 0), (1, 1), (0, 0), (1, 1)] (yoneda @Dot)
    , testProperty "the Yoneda embedding is numbered as a mixed radix" $ do
        -- The weight of every end here. Neither testable kind exercises its two factors together,
        -- 'BOOL' being thin, but over the schema alone both can exceed one. @Yo V (OP E)@ has
        -- @(c -> V)@ paired with @(E -> d)@, which is 2 * 1, 2 * 2, 1 * 1 and 1 * 2.
        expect
          "sizes"
          [2, 4, 1, 2]
          (sizes @(Yo V (OP E)))
        -- and the index agrees with the enumeration where the radix actually carries. The internal
        -- hom depends on this invariant, since it tabulates families against one and reads them
        -- back with the other
        expect "indices" [0, 1, 2, 3] (map (toIndex @(Yo V (OP E)) @E @V) (elements @(Yo V (OP E)) @E @V))
    , testProperty "the subobject classifier counts the sieves of the index category" $
        -- A sieve over @(a, b)@ is a set of pairs @(g : c -> a, h : b -> d)@ closed under
        -- precomposition. Over 'FLS' there is one @g@, over 'TRU' there are two, ordered. Over 'V'
        -- there is one @h@; over 'E' there are three, with 'IdE' above 'Src' and 'Tgt'. Counting the
        -- down-closed subsets of each product gives 5, 2, 14 and 3.
        expect
          "Omega"
          [5, 2, 14, 3]
          (sizes @(Sieve :: GRAPH +-> BOOL))
    ]
