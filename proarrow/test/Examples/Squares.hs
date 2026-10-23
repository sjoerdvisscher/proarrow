-- | Update the value field of every named entry, using square optics. 'field' is a lens,
-- 'each' is a list traversal, and 'fused' combines their witnesses into one absorption.
module Examples.Squares where

import Data.Kind (Type)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude

import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Core ((:~>), type (+->))
import Proarrow.Functor qualified as F
import Proarrow.Limit.BinaryProduct (Product)
import Proarrow.Object (pattern Objs)
import Proarrow.Optic (Prostrong)
import Proarrow.Optic.Traversal (TravFl)
import Proarrow.Path (Path (..))
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Constant (Constant)
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Instance.Star (Star, unStar, pattern Star)
import Proarrow.Profunctor.Representable (Rep (..), RepCostar (..), Representable (..))
import Proarrow.Squares
import Proarrow.Testing (expect, genNamed)
import Props.Hask ()

-- * Data and effects

data Entry a = Entry {entryName :: String, entryValue :: a}
  deriving (Eq, Show)

-- | The list records the old ages, in the order their effects execute.
data Logged a = Logged {visits :: [Int], result :: a}
  deriving (Eq, Show, Functor)

instance Applicative Logged where
  pure = Logged []
  Logged xs f <*> Logged ys x = Logged (xs ++ ys) (f x)

type Effect :: Type +-> Type
type Effect = Star (F.Prelude Logged)

type Point :: Type -> () +-> Type
type Point a = Rep (Constant a)

type Cell :: (Type +-> Type) -> Type -> Type -> Type
type Cell r a b = InputSquare r (Point a) (Point b)

-- | Introduce a primitive effect as a square; 'runCell' is the execution boundary.
primitive :: (a -> Logged b) -> Cell Effect a b
primitive f = mkSquare (\(Id Unit) -> Star (F.Prelude . f))

runCell :: Cell Effect a b -> a -> Logged b
runCell sq = F.unPrelude . unStar (runSquare sq (Id Unit))

-- * The value-field lens

type FieldP :: Type +-> Type
type FieldP = Rep (Product String)
type FieldQ :: Type +-> Type
type FieldQ = Corep (Product String)

fieldUnpackNat :: Point (Entry a) :~> FieldP :.: Point a
fieldUnpackNat (Rep f) = Rep (\x -> let Entry name a = f x in (name, a)) :.: Rep id

fieldRebuildNat :: Point b :~> FieldQ :.: Point (Entry b)
fieldRebuildNat (Rep g) = Corep id :.: Rep (\(name, b) -> Entry name (g b))

fieldUnpack :: Cell FieldP (Entry a) a
fieldUnpack = Sq fieldUnpackNat

fieldRebuild :: Cell FieldQ b (Entry b)
fieldRebuild = Sq fieldRebuildNat

-- | Focus an entry's value while carrying its name as the residual. In the diagram,
-- @s@/@t@ are the entry shapes, @a@/@b@ the value shapes, @p = FieldP@, and
-- @q = FieldQ@. The legs introduce residual effects, which are absorbed below the input.
-- Wire names stay on borders; each contiguous run of @\@@ is one transformation.
--
-- > +-----+-----+-----+
-- > |     |     |     |
-- > s>-@->a>-@->b>-@->t
-- > |  |  |  |  |  |  |
-- > +--p--+--r--+--q--+
-- > |   \    |    /   |
-- > |    @@@@@@@@@    |
-- > |        |        |
-- > +--------r--------+
field :: forall r a b. (Prostrong TravFl r) => Cell r a b -> Cell r (Entry a) (Entry b)
field input =
  fieldUnpack ||| input ||| fieldRebuild
    === proSquare @TravFl @r @FieldP @FieldQ

-- * Traverse a list of entries

type ListP :: Type +-> Type
type ListP = Star []
type ListQ :: Type +-> Type
type ListQ = RepCostar ListP

listUnpackNat :: Point [a] :~> ListP :.: Point a
listUnpackNat f@Objs = tabulate (index f)

listRebuildNat :: Point b :~> ListQ :.: Point [b]
listRebuildNat (Rep g) = RepCostar id :.: Rep (map g)

listUnpack :: Cell ListP [a] a
listUnpack = Sq listUnpackNat

listRebuild :: Cell ListQ b [b]
listRebuild = Sq listRebuildNat

-- | Visit every element, in list order. Its diagram is the same as 'field', with
-- @p = ListP@ and @q = ListQ@. Feeding the output of 'field' into 'each'
-- makes the complete entry update the input square of the list traversal.
each :: forall r a b. (Prostrong TravFl r) => Cell r a b -> Cell r [a] [b]
each input =
  listUnpack ||| input ||| listRebuild
    === proSquare @TravFl @r @ListP @ListQ

-- | A lens inside a traversal, composed by feeding one square program into the other.
entries :: (Prostrong TravFl r) => Cell r a b -> Cell r [Entry a] [Entry b]
entries input = each (field input)

-- * Fuse the two absorptions

type BothP :: Type +-> Type
type BothP = ListP :.: FieldP
type BothQ :: Type +-> Type
type BothQ = FieldQ :.: ListQ

-- | Compose the unpacking squares horizontally, then combine their residual effects.
unpackBoth :: Cell BothP [Entry a] a
unpackBoth =
  listUnpack ||| fieldUnpack
    === vCombineAll @(FieldP ::: ListP ::: Nil)

-- | Rebuilding composes in the other order: the field square precedes the list square.
rebuildBoth :: Cell BothQ b [Entry b]
rebuildBoth =
  fieldRebuild ||| listRebuild
    === vCombineAll @(ListQ ::: FieldQ ::: Nil)

-- | The same update with one absorption for the composed witness pair:
-- @p = ListP :.: FieldP@ and @q = FieldQ :.: ListQ@. Their effects remain vertical
-- or diagonal, including when the witnesses happen to be representable/corepresentable.
-- 'unpackBoth' and 'rebuildBoth' compose the surrounding legs with squares as well.
-- Agreement with 'entries' is the composition law for 'Prostrong'.
--
-- > +-p-+-r-+-q-+
-- > |  \  |  /  |
-- > |   @@@@@   |
-- > |     |     |
-- > +-----r-----+
fused :: forall r a b. (Prostrong TravFl r) => Cell r a b -> Cell r [Entry a] [Entry b]
fused input =
  unpackBoth ||| input ||| rebuildBoth
    === proSquare @TravFl @r @BothP @BothQ

-- * Execute the square program

increment :: Int -> Logged Int
increment age = Logged [age] (age + 1)

-- | Increment both ages, preserving the names and recording the visits as @[36,85]@.
demo :: Logged [Entry Int]
demo = runCell (entries (primitive increment)) [Entry "Ada" 36, Entry "Grace" 85]

test :: TestTree
test =
  testGroup
    "Square programs"
    [ testProperty "field lens preserves the name and visits its value once" $
        expect "field" (Logged [36] (Entry "Ada" 37)) (runCell (field (primitive increment)) (Entry "Ada" 36))
    , testProperty "lens and traversal update each field in list order" $ do
        flags <- genNamed @[Bool] "ages"
        let rows = sampleRows flags
            Logged seen updated = runCell (entries (primitive increment)) rows
        expect "effect order" (map entryValue rows) seen
        expect "names and values" (map (\(Entry name age) -> Entry name (age + 1)) rows) updated
    , testProperty "composed witnesses agree with sequential square optics" $ do
        flags <- genNamed @[Bool] "ages"
        let rows = sampleRows flags
            input = primitive increment
        expect "composition" (runCell (entries input) rows) (runCell (fused input) rows)
    , testProperty "composition also preserves type-changing updates" $ do
        flags <- genNamed @[Bool] "ages"
        let rows = sampleRows flags
            input = primitive (\age -> Logged [age] (show age))
            expected = Logged (map entryValue rows) (map (\(Entry name age) -> Entry name (show age)) rows)
        expect "sequential" expected (runCell (entries input) rows)
        expect "composed" expected (runCell (fused input) rows)
    , testProperty "empty traversal runs no effects" $
        expect "empty" (Logged [] []) (runCell (fused (primitive increment)) [])
    ]

sampleRows :: [Bool] -> [Entry Int]
sampleRows = zipWith (\n b -> Entry (show n) (if b then 7 else 0)) [0 :: Int ..]
