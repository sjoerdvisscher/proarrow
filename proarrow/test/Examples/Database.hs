{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Functorial data migration, worked through the airline example of Fong and Spivak,
-- /Seven Sketches in Compositionality/ (arXiv:1803.05316), section 3.4.3.
--
-- A database __schema__ is a category, an __instance__ of it is a copresheaf, and a functor between
-- schemas induces three migrations: restriction @'Delta'@, and its left and right adjoints
-- @'Sigma'@ and @'Pi'@. None of them needs new machinery here. A functor between kinds is a
-- 'FunctorForRep', which comes with an adjoint pair of profunctors: its conjoint 'Rep' and its
-- companion 'Corep'. Restriction and the left pushforward are then just profunctor composition,
-- and the right pushforward is the right Kan extension that composition is already adjoint to.
--
-- The schemas are the book's: @A@ tells economy seats from first class ones, @B@ does not. Each is
-- the free category on a graph ('PATHS'), so writing one down is writing down its generating arrows
-- and nothing else, and the functor between them is a graph map that 'foldPaths' turns into a
-- functor. Neither carries path equations, and neither can: every arrow lands in an attribute
-- object, and attribute objects have no arrows out, so there are no composable pairs.
--
-- A second pair, @GraphSch@ and @Dds@, is section 3.4.1, the one migration the book works through
-- with tables on both sides. @Dds@ is one point with one arrow looping on it, so it has infinitely
-- many morphisms, one per number of steps; that is the shape a free category is really for.
--
-- The book's own schema, which carries equations, is in "Props.Paths" instead, since what it
-- exercises is the free category's laws rather than migration.
module Examples.Database (test) where

import Control.Monad (unless)
import Data.Type.Equality ((:~:) (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testFailed, testProperty)
import Prelude hiding (id, (.))

import Proarrow.Category.Enriched.Thin (Finite (..), Indexed (..), Member (..), memberIndex)
import Proarrow.Category.Instance.Discrete (DISCRETE (..))
import Proarrow.Category.Instance.Paths (PATHS (..), Paths (..), Rewrite, emb, foldPaths, pathLength)
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Core (Any, CAT, CategoryOf (..), Profunctor (..), Promonad (..), UN, type (+->))
import Proarrow.Functor (Copresheaf, FunctorForRep (..))
import Proarrow.Object (pattern Objs)
import Proarrow.Profunctor.Corepresentable (Corep (..), Corepresentable (corepUniv))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Ran (Ran (..), runRan, type (|>))
import Proarrow.Profunctor.Representable (Rep (..), Representable (repUniv))

-- * The detailed schema @A@

-- | The points of schema @A@: two classes of seat, and the two attribute types. Bare data, with
-- 'DISCRETE' supplying the identity arrows.
type data APoint = EconomyP | FirstClassP | DollarsAP | StringAP

instance Indexed APoint
instance Finite APoint where type Objects APoint = '[EconomyP, FirstClassP, DollarsAP, StringAP]

type A' = DISCRETE APoint

type Economy' = D EconomyP :: A'
type FirstClass' = D FirstClassP :: A'
type DollarsA' = D DollarsAP :: A'
type StringA' = D StringAP :: A'

-- | A singleton for the points. The right pushforward is an end, so 'matchSeats' has to /produce/ a
-- seat at an arbitrary point of this kind, and 'Ob' is what carries which point it has been handed
-- -- so this kind cannot be @(\':~:\')@-arrowed like @B'@, whose 'Ob' is vacuous. 'memberIndex'
-- already refines a point to the one it is, but positionally, so the four positions get names.
type SA (a :: A') = Member a (Objects A')

pattern SEconomy :: () => (a ~ Economy') => SA a
pattern SEconomy = Here

pattern SFirstClass :: () => (a ~ FirstClass') => SA a
pattern SFirstClass = There Here

pattern SDollarsA :: () => (a ~ DollarsA') => SA a
pattern SDollarsA = There (There Here)

pattern SStringA :: () => (a ~ StringA') => SA a
pattern SStringA = There (There (There Here))

{-# COMPLETE SEconomy, SFirstClass, SDollarsA, SStringA #-}

-- | The generating arrows: each class of seat has a price and a position.
type GA :: CAT A'
data GA a b where
  PriceE :: GA Economy' DollarsA'
  PosE :: GA Economy' StringA'
  PriceF :: GA FirstClass' DollarsA'
  PosF :: GA FirstClass' StringA'

-- | No equations: the schema is free on that graph.
instance Rewrite GA

type A = PATHS GA

type Economy = PTH Economy' :: A
type FirstClass = PTH FirstClass' :: A
type DollarsA = PTH DollarsA' :: A
type StringA = PTH StringA' :: A

-- * The merged schema @B@

-- | One class of seat, and the same two attribute types. Nothing maps out of @B'@, so a vacuous
-- 'Ob' is fine here and @(':~:')@ does the job in one line.
type data B' = AirlineSeat' | DollarsB' | StringB'

instance CategoryOf B' where
  type (~>) = (:~:)
  type Ob a = Any a

type GB :: CAT B'
data GB a b where
  PriceB :: GB AirlineSeat' DollarsB'
  PosB :: GB AirlineSeat' StringB'

instance Rewrite GB

type B = PATHS GB

type AirlineSeat = PTH AirlineSeat' :: B

-- * The functor between them

-- | Forget which class a seat is in, on points.
type MergePt :: A' -> B'
type family MergePt a where
  MergePt Economy' = AirlineSeat'
  MergePt FirstClass' = AirlineSeat'
  MergePt DollarsA' = DollarsB'
  MergePt StringA' = StringB'

-- | The functor on the schemas. Only the graph map is given; the universal property of the free
-- category supplies the rest, and there is nothing to check. The object witness is @\\r -> r@
-- because every image is a point of @B@, whose objects are unconstrained.
data family Merge :: A +-> B

instance FunctorForRep Merge where
  type Merge @ x = PTH (MergePt (UN PTH x))
  fmap f@Objs =
    foldPaths @(Rep Merge)
      (\r -> r)
      ( \case
          PriceE -> emb PriceB
          PosE -> emb PosB
          PriceF -> emb PriceB
          PosF -> emb PosB
      )
      f

-- * An instance of the detailed schema

-- | The tables. Two economy seats, two first class ones, and the attribute values they use.
--
-- > Economy | Price | Position       First Class | Price | Position
-- > E1      | 300   | 12A            F1          | 1200  | 2A
-- > E2      | 350   | 14C            F2          | 300   | 12A
type Seats :: Copresheaf A
data Seats u a where
  E1, E2 :: Seats '() Economy
  F1, F2 :: Seats '() FirstClass
  P :: Int -> Seats '() DollarsA
  Pos :: String -> Seats '() StringA

deriving instance Eq (Seats u a)
deriving instance Show (Seats u a)

-- | The table itself, one entry per generating arrow. Acting by @PriceE@ reads the price column of
-- the economy table.
step :: GA a b -> Seats '() (PTH a) -> Seats '() (PTH b)
step PriceE E1 = P 300
step PriceE E2 = P 350
step PosE E1 = Pos "12A"
step PosE E2 = Pos "14C"
step PriceF F1 = P 1200
step PriceF F2 = P 300
step PosF F1 = Pos "2A"
step PosF F2 = Pos "12A"

-- | Functoriality of the instance is that table, walked along a path. The recursion is generic; all
-- the data is in 'step'.
instance Profunctor Seats where
  dimap Unit PNil x = x
  dimap Unit (PCons g rest) x = step g (dimap Unit rest x)
  r \\ s = case s of
    E1 -> r
    E2 -> r
    F1 -> r
    F2 -> r
    P _ -> r
    Pos _ -> r

-- * The three migrations

-- | Restriction: read a @B@-instance as an @A@-instance, by composing with the conjoint.
type Delta :: a +-> b -> Copresheaf b -> Copresheaf a
type Delta f g = g :.: Rep f

-- | The left pushforward: composition with the companion. The coend is the existential of ':.:'.
--
-- That existential does not impose the coend's quotient, which identifies a row with its image
-- under every arrow. Here that costs nothing, because merging the two seat classes relates nothing
-- that was not already equal. It would show for the functor to the one-point schema, section 3.4.4:
-- the book's left pushforward there is the connected components of the emails, and this one would
-- give the plain disjoint union of every row instead. Quotienting by hand is the price of using an
-- existential for a coend, which is the same compromise ':.:' itself documents.
type Sigma :: a +-> b -> Copresheaf a -> Copresheaf b
type Sigma f i = i :.: Corep f

-- | The right pushforward: the right Kan extension along the conjoint. The end is the @forall@ of
-- 'Ran'.
type Pi :: a +-> b -> Copresheaf a -> Copresheaf b
type Pi f i = Rep f |> i

-- | Restriction is lookup at the image object. The coend has nothing to range over once the
-- conjoint is there, so it collapses by coYoneda, and 'toDelta' takes it back.
fromDelta :: (Profunctor j) => Delta f j u x -> j u (f @ x)
fromDelta (j :.: Rep g) = rmap g j

toDelta :: forall {a} {b} (x :: a) (f :: a +-> b) j u. (FunctorForRep f, Ob x) => j u (f @ x) -> Delta f j u x
toDelta j = j :.: repUniv

-- | Every row of an instance turns up in its left pushforward, sitting at the image of the object
-- it came from. This is the unit of @'Sigma' f ⊣ 'Delta' f@ read through 'fromDelta', and it is the
-- whole reason the pushforward is a union: two objects with the same image land in the same table.
toSigma :: forall {a} {b} (x :: a) (f :: a +-> b) i u. (FunctorForRep f, Ob x) => i u x -> Sigma f i u (f @ x)
toSigma i = i :.: corepUniv

-- | Reading one component out of a right pushforward, at the image of the object asked for. This is
-- the counit of @'Delta' f ⊣ 'Pi' f@, so it runs from the pushforward back to the instance, where
-- 'toSigma' runs the other way. Neither direction is a choice: a unit points into its pushforward
-- and a counit out of one, and which of the two a pushforward gets is fixed by the side of
-- restriction it is adjoint on.
fromPi :: forall {a} {b} (x :: a) (f :: a +-> b) i u. (FunctorForRep f, Ob x) => Pi f i u (f @ x) -> i u x
fromPi = runRan repUniv

-- | The same read along an arrow of the target schema rather than at the image object itself. A
-- right pushforward answers one question per arrow into an image, and 'fromPi' is the case where
-- that arrow is the identity.
atPi :: forall {a} {b} (x :: a) (f :: a +-> b) i u c. (FunctorForRep f, Ob x) => (c ~> f @ x) -> Pi f i u c -> i u x
atPi g = runRan (Rep g)

-- * The left pushforward is the union

-- | Every seat of either class becomes an airline seat. Nothing here says which table a seat came
-- from: 'toSigma' sends it to the image of its own object, and both seat objects have the same
-- image, so all four land in one table.
mergedSeats :: [Sigma Merge Seats '() AirlineSeat]
mergedSeats = [toSigma E1, toSigma E2, toSigma F1, toSigma F2]

-- | Read a merged seat back, by asking the singleton which table it came from. Only the two seat
-- objects can appear: an attribute object would need an arrow from @DollarsB@ or @StringB@ to
-- @AirlineSeat@, and the schema has none, so those cases are unreachable and need no equation.
seatName :: Sigma Merge Seats '() AirlineSeat -> String
seatName (s :.: Corep @a PNil) = case memberIndex @(UN PTH a) of
  SEconomy -> "economy " ++ show s
  SFirstClass -> "first class " ++ show s

-- * Restriction duplicates

-- | One merged seat, read back as an economy row and as a first class row. The two definitions are
-- the same expression at two different types, which is the duplication the book describes: both
-- seat objects have image @AirlineSeat@, so 'toDelta' accepts the same seat for either.
economyRow :: Delta Merge (Sigma Merge Seats) '() Economy
economyRow = toDelta (toSigma E1)

firstClassRow :: Delta Merge (Sigma Merge Seats) '() FirstClass
firstClassRow = toDelta (toSigma E1)

-- | And one reader serves both, for the same reason.
readRow :: (Merge @ x ~ AirlineSeat) => Delta Merge (Sigma Merge Seats) '() x -> String
readRow = seatName . fromDelta

-- * The right pushforward is the join

-- | A pair of seats, one of each class, as an element of the right pushforward at @AirlineSeat@.
--
-- Only the pair is data. The two attribute components are forced: they are read off the economy
-- seat by the instance's own functoriality. What makes reading them off the first class seat give
-- the same answer is the end condition, and that is exactly the agreement tested for here, so this
-- returns 'Nothing' for a pair that does not agree rather than building an ill-formed element.
matchSeats :: Seats '() Economy -> Seats '() FirstClass -> Maybe (Pi Merge Seats '() AirlineSeat)
matchSeats e f
  | dimap Unit (emb PriceE) e == dimap Unit (emb PriceF) f
  , dimap Unit (emb PosE) e == dimap Unit (emb PosF) f =
      Just
        ( Ran \(Rep @x _) -> case memberIndex @(UN PTH x) of
            SEconomy -> e
            SFirstClass -> f
            SDollarsA -> dimap Unit (emb PriceE) e
            SStringA -> dimap Unit (emb PosE) e
        )
  | otherwise = Nothing

-- | The join: every pair of seats that agrees on both attributes.
theJoin :: [Pi Merge Seats '() AirlineSeat]
theJoin = [p | e <- [E1, E2], f <- [F1, F2], Just p <- [matchSeats e f]]

-- * Restriction from a schema with infinitely many arrows

-- | Section 3.4.1. The graph schema: an arrow has a source and a target vertex.
type data GR' = Arrow' | Vertex'

instance CategoryOf GR' where
  type (~>) = (:~:)
  type Ob a = Any a

type GGr :: CAT GR'
data GGr a b where
  Source :: GGr Arrow' Vertex'
  Target :: GGr Arrow' Vertex'

instance Rewrite GGr

type GraphSch = PATHS GGr

type Arrow = PTH Arrow' :: GraphSch
type Vertex = PTH Vertex' :: GraphSch

-- | The discrete dynamical system schema: one point, one arrow from it to itself. Its morphisms are
-- the powers of that arrow, so unlike every other schema here it has infinitely many of them. A
-- free category gives them for nothing; a hand-written morphism type would have to index by a
-- number and re-derive composition.
type data DDS' = State'

instance CategoryOf DDS' where
  type (~>) = (:~:)
  type Ob a = Any a

type GDds :: CAT DDS'
data GDds a b where
  Next :: GDds State' State'

instance Rewrite GDds

type Dds = PATHS GDds

type State = PTH State' :: Dds

twoSteps :: State ~> State
twoSteps = emb Next . emb Next

-- | Both points of the graph schema go to the single state, the source arrow to the identity and
-- the target arrow to one step of the machine.
type FPt :: GR' -> DDS'
type family FPt a where
  FPt Arrow' = State'
  FPt Vertex' = State'

data family Unroll :: GraphSch +-> Dds

instance FunctorForRep Unroll where
  type Unroll @ x = PTH (FPt (UN PTH x))
  fmap f@Objs =
    foldPaths @(Rep Unroll)
      (\r -> r)
      ( \case
          Source -> id
          Target -> emb Next
      )
      f

-- | The machine of equation 3.65: seven states, each with a next.
--
-- > State | next     State | next
-- > 1     | 4        5     | 5
-- > 2     | 4        6     | 7
-- > 3     | 5        7     | 6
-- > 4     | 5
type Machine :: Copresheaf Dds
data Machine u a where
  St1, St2, St3, St4, St5, St6, St7 :: Machine '() State

deriving instance Eq (Machine u a)
deriving instance Show (Machine u a)

machineStep :: GDds a b -> Machine '() (PTH a) -> Machine '() (PTH b)
machineStep Next St1 = St4
machineStep Next St2 = St4
machineStep Next St3 = St5
machineStep Next St4 = St5
machineStep Next St5 = St5
machineStep Next St6 = St7
machineStep Next St7 = St6

instance Profunctor Machine where
  dimap Unit PNil x = x
  dimap Unit (PCons g rest) x = machineStep g (dimap Unit rest x)
  r \\ s = case s of
    St1 -> r
    St2 -> r
    St3 -> r
    St4 -> r
    St5 -> r
    St6 -> r
    St7 -> r

states :: [Machine '() State]
states = [St1, St2, St3, St4, St5, St6, St7]

-- | Restricting the machine along that functor turns it into a graph. Both tables hold the states,
-- because both points have the same image, and the source and target columns are read off by the
-- restricted instance's own functoriality rather than by hand.
type Graph = Delta Unroll Machine

asArrow :: Machine '() State -> Graph '() Arrow
asArrow = toDelta

sourceOf, targetOf :: Graph '() Arrow -> Graph '() Vertex
sourceOf = dimap Unit (emb Source)
targetOf = dimap Unit (emb Target)

test :: TestTree
test =
  testGroup
    "Database"
    [ testProperty "the left pushforward unions the two seat tables" $
        unless
          (map seatName mergedSeats == ["economy E1", "economy E2", "first class F1", "first class F2"])
          (testFailed "the merged table should hold all four seats, tagged by where they came from")
    , testProperty "restriction copies a merged seat into both tables" $ do
        unless (readRow economyRow == "economy E1") (testFailed "E1 should appear as an economy row")
        unless (readRow firstClassRow == "economy E1") (testFailed "E1 should appear as a first class row too")
    , testProperty "the right pushforward joins the two tables" $ case theJoin of
        [p] -> do
          unless (fromPi @Economy p == E1) (testFailed "the economy half should be E1")
          unless (fromPi @FirstClass p == F2) (testFailed "the first class half should be F2")
          unless (atPi @DollarsA (emb PriceB) p == P 300) (testFailed "the shared price should be 300")
          unless (atPi @StringA (emb PosB) p == Pos "12A") (testFailed "the shared position should be 12A")
        ps -> testFailed ("exactly one pair of seats agrees, found " ++ show (length ps))
    , testProperty "restriction turns the machine into the book's graph" $ do
        unless
          (map (fromDelta . sourceOf . asArrow) states == states)
          (testFailed "the source column should be the identity")
        unless
          (map (fromDelta . targetOf . asArrow) states == [St4, St4, St5, St5, St5, St7, St6])
          (testFailed "the target column should be one step of the machine")
        unless (pathLength twoSteps == 2) (testFailed "the loop schema should have a two-step arrow")
    ]
