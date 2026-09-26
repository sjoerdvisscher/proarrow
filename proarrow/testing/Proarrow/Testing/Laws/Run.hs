{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Checking laws stated as code ("Proarrow.Tools.Laws") in a 'Testable' category: 'testLaws'
-- runs each law with random objects for its variables and random arrows for the ones it asks for,
-- and compares both sides.
--
-- The endpoints of a law's equation are built inside the law, so their 'TestOb' cannot be listed
-- up front. Instead the law is run in 'TESTED' @k@, whose objects are built from leaves by the
-- structures' object formers; there an object's 'Ob' is 'Tested', which rebuilds the 'TestOb' of
-- the object of @k@ it stands for from the 'Witnesses' passed at run time: one 'Witness' per
-- structure in the law's list, e.g. a 'WithTestOb2' for 'M.Monoidal'.
--
-- A structure this module does not cover can be added from outside it, in the same way as the ones
-- here:
--
-- * a former for each new kind of object (an open data family, or one of the free category's),
--   with a 'Tested' instance giving its 'Untest' and rebuilding its 'Ob' and 'TestOb';
-- * a 'Witness' instance for the structure, holding how 'TestOb' is closed under its formers;
-- * the structure's class instance for 'TESTED', whose arrows describe themselves ('prim' for a
--   named arrow, 'app', 'infixlDoc', 'infixrDoc' for operations on arrows).
module Proarrow.Testing.Laws.Run
  ( testLaws
  , testLawsWith
  , testProLaws

    -- * Witnesses
  , Witness (..)
  , Witnesses (..)
  , HasWitness (..)

    -- * Interpreting with testable objects
  , TESTED (..)
  , Tested (..)
  , untestOb2
  , untestOb3
  , untestTestOb2
  , TestedArr
  , pattern TestedArr

    -- * Interpreting profunctors
  , TestedP (..)
  , RepF
  , RepresentedBy

    -- * Describing arrows
  , Doc
  , prim
  , atom
  , app
  , apps
  , infixlDoc
  , infixrDoc
  ) where

import Data.Kind (Constraint, Type)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (Property, TestOptions, testProperty, testPropertyWith)
import Prelude hiding (fst, id, snd, (.))

import Proarrow.Category.Instance.Free qualified as Free
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Category.Monoidal.Closed qualified as Exponential
import Proarrow.Category.Monoidal.CompactClosed qualified as CC
import Proarrow.Category.Monoidal.CopyDiscard qualified as CopyDiscard
import Proarrow.Category.Monoidal.Distributive qualified as Distributive
import Proarrow.Category.Monoidal.StarAutonomous qualified as SA
import Proarrow.Category.Monoidal.Strength qualified as Strength
import Proarrow.Colimit.BinaryCoproduct qualified as BinaryCoproduct
import Proarrow.Colimit.Initial qualified as Initial
import Proarrow.Core (CAT, CategoryOf (..), Hom, Kind, Profunctor (..), Promonad (..), type (+->))
import Proarrow.Limit.BinaryProduct qualified as BinaryProduct
import Proarrow.Limit.Terminal qualified as Terminal
import Proarrow.Monoid qualified as Monoid
import Proarrow.Profunctor.Representable (Representable (..), withObRep)
import Proarrow.Testing
  ( Some (..)
  , SomeProfunctorElt (..)
  , Testable (..)
  , TestableProfunctor (..)
  , TestableTypeP
  , WithTestOb2
  , WithTestObCoprod
  , WithTestObDual
  , WithTestObExp
  , WithTestObProd
  , WithTestObRep
  , genNamed
  , genOb
  , genObSuchThat
  , isGenNonEmpty
  , obFromTestOb
  , testEq
  )
import Proarrow.Tools.Laws qualified as Laws

-- | Check the laws of @'Laws.Laws' cs@ in @k@, one property per law: run each law in 'TESTED'
-- with random objects for its variables and random arrows for the ones it asks for. The
-- 'Witnesses' say how 'TestOb' is closed under the structures of @cs@ (see 'Tested').
testLaws :: forall cs k. (Laws.Laws cs, Testable k, Free.All cs (TESTED cs k)) => String -> Witnesses cs k -> TestTree
testLaws = testLawsWith @cs (genOb @k)

-- | 'testLaws' with the objects for the variables drawn from the given generator, e.g.
-- 'Proarrow.Testing.genObSmall' where the laws build large objects like exponentials.
testLawsWith
  :: forall cs k
   . (Laws.Laws cs, Testable k, Free.All cs (TESTED cs k))
  => Property (Some k) -> String -> Witnesses cs k -> TestTree
testLawsWith genObject name witnesses =
  testGroup name [testProperty (Laws.lawName law) (checkLaw law) | law <- Laws.laws @cs]
  where
    checkLaw :: Laws.Law cs -> Property ()
    checkLaw (Laws.Law lawName body) = do
      Some @a <- genObject
      Some @b <- genObject
      Some @c <- genObject
      Some @d <- genObject
      Some @e <- genObject
      eq <-
        body @(TLeaf a :: TESTED cs k) @(TLeaf b) @(TLeaf c) @(TLeaf d) @(TLeaf e) (genArr witnesses)
      testEquation witnesses lawName eq

-- | Check the laws of @'Laws.ProLaws' c@ for the profunctor @p@, one property per law: run each
-- law with @p@ interpreted as 'TestedP' @p@, its elements drawn by 'genProfunctorElt' (each picks
-- its two object variables), the other variables of a 'Laws.ProLaw' drawn along the chain
-- @e '~>' c '~>' a@ and @b '~>' d '~>' f@ where those hom-sets are non-empty, and random arrows
-- for the ones it asks for. The two 'Witnesses' are for the domain @j@ and the codomain
-- @k@ of @p@, and the 'TestOptions' apply to each law's property.
testProLaws
  :: forall {j} {k} csj csk cl (p :: j +-> k)
   . (Laws.ProLaws cl, TestableProfunctor p, cl (TestedP p :: TESTED csj j +-> TESTED csk k))
  => TestOptions -> String -> Witnesses csj j -> Witnesses csk k -> TestTree
testProLaws opts name wsj wsk =
  testGroup name [testPropertyWith opts (Laws.proLawName law) (checkLaw law) | law <- Laws.proLaws @cl]
  where
    checkLaw :: Laws.ProLaw cl -> Property ()
    checkLaw (Laws.ProLaw lawName body) = do
      SomeP @a @b p0 <- genProfunctorElt @p "p"
      Some @c <- genObSuchThat @k \(Some @c') -> isGenNonEmpty @(c' ~> a)
      Some @d <- genObSuchThat @j \(Some @d') -> isGenNonEmpty @(b ~> d')
      Some @e <- genObSuchThat @k \(Some @e') -> isGenNonEmpty @(e' ~> c)
      Some @f <- genObSuchThat @j \(Some @f') -> isGenNonEmpty @(d ~> f')
      eq <-
        body @(TestedP p) @(TLeaf a :: TESTED csk k) @(TLeaf b :: TESTED csj j) @(TLeaf c) @(TLeaf d) @(TLeaf e) @(TLeaf f)
          (prim "p" p0)
          (genArr wsk)
          (genArr wsj)
      testProEquation lawName eq
    checkLaw (Laws.ProLaw3 lawName body) = do
      SomeP @a @b p0 <- genProfunctorElt @p "p"
      SomeP @c @d p1 <- genProfunctorElt @p "p'"
      SomeP @e @f p2 <- genProfunctorElt @p "p''"
      eq <-
        body @(TestedP p) @(TLeaf a :: TESTED csk k) @(TLeaf b :: TESTED csj j) @(TLeaf c) @(TLeaf d) @(TLeaf e) @(TLeaf f)
          (prim "p" p0)
          (prim "p'" p1)
          (prim "p''" p2)
          (genArr wsk)
          (genArr wsj)
      testProEquation lawName eq
    testProEquation :: String -> Laws.ProEquation (TestedP p :: TESTED csj j +-> TESTED csk k) -> Property ()
    testProEquation lawName = \case
      l Laws.:=: r -> testTested wsj wsk lawName l r
      Laws.InK e -> testEquation wsk lawName e
      Laws.InJ e -> testEquation wsj lawName e

-- | Compare the two sides of an equation between arrows of 'TESTED', printing them on failure.
testEquation :: forall cs k. (Testable k) => Witnesses cs k -> String -> Laws.Equation (TESTED cs k) -> Property ()
testEquation ws lawName eq = Laws.withSides eq (testTested ws ws lawName)

-- | A named arbitrary element of @p@ between the objects of @k@ and @j@ that the endpoints stand
-- for. With @p@ the hom profunctor, a named arbitrary arrow.
genTested
  :: forall {csj} {csk} {j} {k} (p :: j +-> k) (x :: TESTED csk k) (y :: TESTED csj j)
   . (TestableTypeP p, Tested x, Tested y)
  => Witnesses csj j -> Witnesses csk k -> String -> Property (TestedP p x y)
genTested wsj wsk s = untestTestOb @x wsk $ untestTestOb @y wsj $ prim s <$> genNamed @(p (Untest x) (Untest y)) s

-- | A named arbitrary arrow, 'genTested' at the hom profunctor.
genArr
  :: forall cs k (x :: TESTED cs k) y. (Testable k, Tested x, Tested y) => Witnesses cs k -> String -> Property (x ~> y)
genArr ws = genTested @(Hom k) ws ws

-- | Compare two elements of @p@, printing their descriptions on failure.
testTested
  :: forall {csj} {csk} {j} {k} (p :: j +-> k) (x :: TESTED csk k) (y :: TESTED csj j)
   . (TestableProfunctor p)
  => Witnesses csj j -> Witnesses csk k -> String -> TestedP p x y -> TestedP p x y -> Property ()
testTested wsj wsk lawName (TestedP dl l) (TestedP dr r) =
  untestTestOb @x wsk $ untestTestOb @y @(Property ()) wsj $ testEq lawName (dl 0 "") l (dr 0 "") r

-- | Objects of @k@ built from leaves by the structures' object formers. Checking a law
-- interprets it here rather than in @k@ itself: an object's 'Ob' is then 'Tested', which
-- recovers the 'TestOb' of the object of @k@ it stands for ('Untest') from the 'Witnesses' for
-- the structures @cs@, supplied at run time.
--
-- The only constructor is the leaf. Compound objects use the free category's formers, which are
-- open data families of any kind ('M.**!', 'BinaryProduct.*!', 'SA.DualF', ...), so a new
-- structure brings its own former and its own 'Tested' instance.
type TESTED :: [Kind -> Constraint] -> Kind -> Kind
type data TESTED cs k = TLeaf k

-- * Witnesses

-- | How 'TestOb' is closed under the object formers of the structure @c@, for the category @k@.
-- Structures without formers of their own have a witness that holds nothing.
type Witness :: (Kind -> Constraint) -> Kind -> Type
data family Witness c k

data instance Witness CategoryOf k = CategoryW
newtype instance Witness M.Monoidal k = MonoidalW (WithTestOb2 k)
data instance Witness M.SymMonoidal k = SymMonoidalW
newtype instance Witness BinaryProduct.HasBinaryProducts k = ProductsW (WithTestObProd k)
newtype instance Witness BinaryCoproduct.HasBinaryCoproducts k = CoproductsW (WithTestObCoprod k)
data instance Witness Terminal.HasTerminalObject k = TerminalW
data instance Witness Initial.HasInitialObject k = InitialW
data instance Witness Distributive.Distributive k = DistributiveW
newtype instance Witness Exponential.Closed k = ClosedW (WithTestObExp k)
newtype instance Witness SA.StarAutonomous k = StarAutonomousW (WithTestObDual k)
data instance Witness CC.CompactClosed k = CompactClosedW
data instance Witness Strength.TracedMonoidal k = TracedW
data instance Witness CopyDiscard.CopyDiscard k = CopyDiscardW
data instance Witness (Monoid.Supplies Monoid.Monoid) k = MonoidSupplyW
data instance Witness (Monoid.Supplies Monoid.Comonoid) k = ComonoidSupplyW
data instance Witness (Monoid.Supplies Monoid.CommutativeMonoid) k = CommutativeMonoidSupplyW
data instance Witness (Monoid.Supplies Monoid.CocommutativeComonoid) k = CocommutativeComonoidSupplyW

infixr 5 :&

-- | One 'Witness' for each structure in @cs@, in the same order.
type Witnesses :: [Kind -> Constraint] -> Kind -> Type
data Witnesses cs k where
  WNil :: Witnesses '[] k
  (:&) :: Witness c k -> Witnesses cs k -> Witnesses (c ': cs) k

-- | Look up the witness for the structure @c@.
type HasWitness :: (Kind -> Constraint) -> [Kind -> Constraint] -> Constraint
class HasWitness c cs where
  -- | The witness for @c@ in the list.
  witness :: Witnesses cs k -> Witness c k

instance {-# OVERLAPPABLE #-} (HasWitness c cs) => HasWitness c (d ': cs) where
  witness (_ :& ws) = witness @c ws
instance HasWitness c (c ': cs) where
  witness (w :& _) = w

-- * The testable-objects category

-- | The objects of 'TESTED': those that stand for an object of @k@ ('Untest'), with how to
-- rebuild that object's 'Ob' and 'TestOb' from the ones of its parts. This is 'Ob' for 'TESTED'.
type Tested :: forall {cs} {k}. TESTED cs k -> Constraint
class Tested (a :: TESTED cs k) where
  -- | The object of @k@ that @a@ stands for. (The class variable is re-annotated so that @k@ is
  -- in scope in the result kind.)
  type Untest (a :: TESTED cs k) :: k

  -- | The 'Ob' of the object @a@ stands for, which the structures of @k@ provide.
  untestOb :: ((Ob (Untest a)) => r) -> r

  -- | The 'TestOb' of the object @a@ stands for, which the witnesses provide.
  untestTestOb :: Witnesses cs k -> ((TestOb (Untest a)) => r) -> r

instance (Testable k, TestOb (a :: k)) => Tested (TLeaf a :: TESTED cs k) where
  type Untest (TLeaf a) = a
  untestOb r = obFromTestOb @a r
  untestTestOb _ r = r
instance (Testable k, M.Monoidal k, TestOb (M.Unit :: k)) => Tested (M.UnitF :: TESTED cs k) where
  type Untest M.UnitF = M.Unit
  untestOb r = r
  untestTestOb _ r = r
instance (HasWitness M.Monoidal cs, M.Monoidal k, Tested (a :: TESTED cs k), Tested b) => Tested (a M.**! b) where
  type Untest (a M.**! b) = Untest a M.** Untest b
  untestOb r = untestOb2 @a @b (M.withOb2 @k @(Untest a) @(Untest b) r)
  untestTestOb ws r = untestTestOb2 @a @b ws (case witness @M.Monoidal ws of MonoidalW f -> f @(Untest a) @(Untest b) r)
instance
  (HasWitness BinaryProduct.HasBinaryProducts cs, BinaryProduct.HasBinaryProducts k, Tested (a :: TESTED cs k), Tested b)
  => Tested (a BinaryProduct.*! b)
  where
  type Untest (a BinaryProduct.*! b) = Untest a BinaryProduct.&& Untest b
  untestOb r = untestOb2 @a @b (BinaryProduct.withObProd @k @(Untest a) @(Untest b) r)
  untestTestOb ws r =
    untestTestOb2 @a @b ws (case witness @BinaryProduct.HasBinaryProducts ws of ProductsW f -> f @(Untest a) @(Untest b) r)
instance (Testable k, Initial.HasInitialObject k, TestOb (Initial.InitialObject :: k)) => Tested (Initial.InitF :: TESTED cs k) where
  type Untest Initial.InitF = Initial.InitialObject
  untestOb r = r
  untestTestOb _ r = r
instance
  ( HasWitness BinaryCoproduct.HasBinaryCoproducts cs
  , BinaryCoproduct.HasBinaryCoproducts k
  , Tested (a :: TESTED cs k)
  , Tested b
  )
  => Tested (a BinaryCoproduct.+ b)
  where
  type Untest (a BinaryCoproduct.+ b) = Untest a BinaryCoproduct.|| Untest b
  untestOb r = untestOb2 @a @b (BinaryCoproduct.withObCoprod @k @(Untest a) @(Untest b) r)
  untestTestOb ws r =
    untestTestOb2 @a @b
      ws
      (case witness @BinaryCoproduct.HasBinaryCoproducts ws of CoproductsW f -> f @(Untest a) @(Untest b) r)

instance
  (Testable k, Terminal.HasTerminalObject k, TestOb (Terminal.TerminalObject :: k))
  => Tested (Terminal.TermF :: TESTED cs k)
  where
  type Untest Terminal.TermF = Terminal.TerminalObject
  untestOb r = r
  untestTestOb _ r = r
instance
  (HasWitness Exponential.Closed cs, Exponential.Closed k, Tested (a :: TESTED cs k), Tested b)
  => Tested (a Exponential.--> b)
  where
  type Untest (a Exponential.--> b) = Untest a Exponential.~~> Untest b
  untestOb r = untestOb2 @a @b (Exponential.withObExp @k @(Untest a) @(Untest b) r)
  untestTestOb ws r =
    untestTestOb2 @a @b ws (case witness @Exponential.Closed ws of ClosedW f -> f @(Untest a) @(Untest b) r)

instance (HasWitness SA.StarAutonomous cs, SA.StarAutonomous k, Tested (a :: TESTED cs k)) => Tested (SA.DualF a) where
  type Untest (SA.DualF a) = SA.Dual (Untest a)
  untestOb r = untestOb @a (SA.withObDual @k @(Untest a) r)
  untestTestOb ws r = untestTestOb @a ws (case witness @SA.StarAutonomous ws of StarAutonomousW f -> f @(Untest a) r)

-- | 'untestOb' of two objects at once.
untestOb2 :: forall {cs} {k} (a :: TESTED cs k) b r. (Tested a, Tested b) => ((Ob (Untest a), Ob (Untest b)) => r) -> r
untestOb2 r = untestOb @a (untestOb @b r)

-- | 'untestTestOb' of two objects at once.
untestTestOb2
  :: forall {cs} {k} (a :: TESTED cs k) (b :: TESTED cs k) r
   . (Tested a, Tested b) => Witnesses cs k -> ((TestOb (Untest a), TestOb (Untest b)) => r) -> r
untestTestOb2 ws r = untestTestOb @a ws (untestTestOb @b ws r)

-- | 'untestOb' of three objects at once.
untestOb3
  :: forall {cs} {k} (a :: TESTED cs k) b c r
   . (Tested a, Tested b, Tested c) => ((Ob (Untest a), Ob (Untest b), Ob (Untest c)) => r) -> r
untestOb3 r = untestOb @a (untestOb @b (untestOb @c r))

-- | An arrow of @k@ between the objects the endpoints stand for, with a description of how it was
-- built: an element of the hom profunctor. These are the arrows of 'TESTED'.
type TestedArr :: forall cs k. CAT (TESTED cs k)
type TestedArr @cs @k = TestedP (Hom k)

-- | 'TestedP' at the hom profunctor.
pattern TestedArr
  :: forall cs k (a :: TESTED cs k) (b :: TESTED cs k)
   . () => (Tested a, Tested b) => Doc -> Untest a ~> Untest b -> TestedArr a b
pattern TestedArr d f = TestedP d f

{-# COMPLETE TestedArr #-}

-- | A description that can be shown at a precedence, like 'showsPrec'.
type Doc = Int -> ShowS

-- | A name, which never needs parentheses.
atom :: String -> Doc
atom s _ = showString s

-- | An element or arrow described by its name.
prim :: (Tested a, Tested b) => String -> p (Untest a) (Untest b) -> TestedP p a b
prim s = TestedP (atom s)

-- | A function applied to one argument.
app :: String -> Doc -> Doc
app f x = apps f [x]

-- | A function applied to several arguments.
apps :: String -> [Doc] -> Doc
apps f xs d = showParen (d > 10) (showString f . foldr (\x r -> showChar ' ' . x 11 . r) (\r -> r) xs)

-- | A left or right associative infix operator at the given precedence, like @infixl@ and
-- @infixr@. The operator string includes its surrounding spaces, e.g. @" . "@.
infixlDoc, infixrDoc :: Int -> String -> Doc -> Doc -> Doc
infixlDoc p op x y d = showParen (d > p) (x p . showString op . y (p + 1))
infixrDoc p op x y d = showParen (d > p) (x (p + 1) . showString op . y p)

instance (CategoryOf k) => CategoryOf (TESTED cs k) where
  type (~>) = TestedArr
  type Ob a = Tested a

instance
  ( HasWitness M.Monoidal csj
  , HasWitness M.Monoidal csk
  , Testable j
  , Testable k
  , M.MonoidalProfunctor p
  , TestOb (M.Unit :: j)
  , TestOb (M.Unit :: k)
  )
  => M.MonoidalProfunctor (TestedP p :: TESTED csj j +-> TESTED csk k)
  where
  one = prim "one" M.one
  TestedP df f ** TestedP dg g = TestedP (infixlDoc 8 " ** " df dg) (f M.** g)
instance (HasWitness M.Monoidal cs, Testable k, M.Monoidal k, TestOb (M.Unit :: k)) => M.Monoidal (TESTED cs k) where
  type Unit = M.UnitF
  type a ** b = a M.**! b
  withOb2 r = r
  leftUnitor @a = untestOb @a (prim "leftUnitor" M.leftUnitor)
  leftUnitorInv @a = untestOb @a (prim "leftUnitorInv" M.leftUnitorInv)
  rightUnitor @a = untestOb @a (prim "rightUnitor" M.rightUnitor)
  rightUnitorInv @a = untestOb @a (prim "rightUnitorInv" M.rightUnitorInv)
  associator @a @b @c = untestOb3 @a @b @c (prim "associator" (M.associator @k @(Untest a) @(Untest b) @(Untest c)))
  associatorInv @a @b @c = untestOb3 @a @b @c (prim "associatorInv" (M.associatorInv @k @(Untest a) @(Untest b) @(Untest c)))
instance (HasWitness M.Monoidal cs, Testable k, M.SymMonoidal k, TestOb (M.Unit :: k)) => M.SymMonoidal (TESTED cs k) where
  swap @a @b = untestOb2 @a @b (prim "swap" (M.swap @k @(Untest a) @(Untest b)))

instance
  (HasWitness BinaryProduct.HasBinaryProducts cs, BinaryProduct.HasBinaryProducts k)
  => BinaryProduct.HasBinaryProducts (TESTED cs k)
  where
  type a && b = a BinaryProduct.*! b
  withObProd r = r
  fst @a @b = untestOb2 @a @b (prim "fst" (BinaryProduct.fst @k @(Untest a) @(Untest b)))
  snd @a @b = untestOb2 @a @b (prim "snd" (BinaryProduct.snd @k @(Untest a) @(Untest b)))
  TestedArr df f &&& TestedArr dg g = TestedArr (infixlDoc 5 " &&& " df dg) (f BinaryProduct.&&& g)

instance (Testable k, Initial.HasInitialObject k, TestOb (Initial.InitialObject :: k)) => Initial.HasInitialObject (TESTED cs k) where
  type InitialObject = Initial.InitF
  initiate @a = untestOb @a (prim "initiate" Initial.initiate)

instance
  (HasWitness BinaryCoproduct.HasBinaryCoproducts cs, BinaryCoproduct.HasBinaryCoproducts k)
  => BinaryCoproduct.HasBinaryCoproducts (TESTED cs k)
  where
  type a || b = a BinaryCoproduct.+ b
  withObCoprod r = r
  lft @a @b = untestOb2 @a @b (prim "lft" (BinaryCoproduct.lft @k @(Untest a) @(Untest b)))
  rgt @a @b = untestOb2 @a @b (prim "rgt" (BinaryCoproduct.rgt @k @(Untest a) @(Untest b)))
  TestedArr df f ||| TestedArr dg g = TestedArr (infixlDoc 4 " ||| " df dg) (f BinaryCoproduct.||| g)

instance
  ( HasWitness M.Monoidal cs
  , HasWitness BinaryCoproduct.HasBinaryCoproducts cs
  , Testable k
  , Distributive.Distributive k
  , TestOb (M.Unit :: k)
  , TestOb (Initial.InitialObject :: k)
  )
  => Distributive.Distributive (TESTED cs k)
  where
  distL @a @b @c = untestOb3 @a @b @c (prim "distL" (Distributive.distL @k @(Untest a) @(Untest b) @(Untest c)))
  distR @a @b @c = untestOb3 @a @b @c (prim "distR" (Distributive.distR @k @(Untest a) @(Untest b) @(Untest c)))
  absorbL @a = untestOb @a (prim "absorbL" (Distributive.absorbL @k @(Untest a)))
  absorbR @a = untestOb @a (prim "absorbR" (Distributive.absorbR @k @(Untest a)))

instance
  (Testable k, Terminal.HasTerminalObject k, TestOb (Terminal.TerminalObject :: k))
  => Terminal.HasTerminalObject (TESTED cs k)
  where
  type TerminalObject = Terminal.TermF
  terminate @a = untestOb @a (prim "terminate" Terminal.terminate)

instance
  (HasWitness M.Monoidal cs, HasWitness Exponential.Closed cs, Testable k, Exponential.Closed k, TestOb (M.Unit :: k))
  => Exponential.Closed (TESTED cs k)
  where
  type a ~~> b = a Exponential.--> b
  withObExp r = r
  curry @a @b (TestedArr df f) = untestOb2 @a @b (TestedArr (app "curry" df) (Exponential.curry @k @(Untest a) @(Untest b) f))
  apply @a @b = untestOb2 @a @b (prim "apply" (Exponential.apply @k @(Untest a) @(Untest b)))

  -- '^^^' is infixl 9 and '.' infixr 9, so '^^^' is parenthesized under either side of '.'.
  TestedArr df f ^^^ TestedArr dg g =
    TestedArr (\d -> showParen (d >= 9) (df 9 . showString " ^^^ " . dg 10)) (f Exponential.^^^ g)

instance
  ( HasWitness M.Monoidal cs
  , HasWitness Exponential.Closed cs
  , HasWitness SA.StarAutonomous cs
  , Testable k
  , SA.StarAutonomous k
  , TestOb (M.Unit :: k)
  )
  => SA.StarAutonomous (TESTED cs k)
  where
  type Dual a = SA.DualF a
  withObDual r = r
  dual (TestedArr df f) = TestedArr (app "dual" df) (SA.dual f)
  dualInv @a @b (TestedArr df f) = untestOb2 @a @b (TestedArr (app "dualInv" df) (SA.dualInv @k @(Untest a) @(Untest b) f))
  linDist @a @b @c (TestedArr df f) =
    untestOb3 @a @b @c (TestedArr (app "linDist" df) (SA.linDist @k @(Untest a) @(Untest b) @(Untest c) f))
  linDistInv @a @b @c (TestedArr df f) =
    untestOb3 @a @b @c (TestedArr (app "linDistInv" df) (SA.linDistInv @k @(Untest a) @(Untest b) @(Untest c) f))
  doubleNeg @a = untestOb @a (prim "doubleNeg" (SA.doubleNeg @k @(Untest a)))
  doubleNegInv @a = untestOb @a (prim "doubleNegInv" (SA.doubleNegInv @k @(Untest a)))

instance
  ( HasWitness M.Monoidal cs
  , HasWitness Exponential.Closed cs
  , HasWitness SA.StarAutonomous cs
  , Testable k
  , CC.CompactClosed k
  , TestOb (M.Unit :: k)
  )
  => CC.CompactClosed (TESTED cs k)
  where
  distribDual @a @b = untestOb2 @a @b (prim "distribDual" (CC.distribDual @k @(Untest a) @(Untest b)))
  dualUnit = prim "dualUnit" CC.dualUnit
  dualityUnit @a = untestOb @a (prim "dualityUnit" (CC.dualityUnit @k @(Untest a)))
  dualityCounit @a = untestOb @a (prim "dualityCounit" (CC.dualityCounit @k @(Untest a)))

-- | Every object is a monoid when the category supplies them, with the monoid of the object it
-- stands for.
instance
  (HasWitness M.Monoidal cs, Testable k, M.Monoidal k, Monoid.Supplies Monoid.Monoid k, TestOb (M.Unit :: k), Tested a)
  => Monoid.Monoid (a :: TESTED cs k)
  where
  mempty = untestOb @a (prim "mempty" (Monoid.mempty @(Untest a)))
  mappend = untestOb @a (prim "mappend" (Monoid.mappend @(Untest a)))

-- | Every object is a comonoid when the category supplies them.
instance
  (HasWitness M.Monoidal cs, Testable k, M.Monoidal k, Monoid.Supplies Monoid.Comonoid k, TestOb (M.Unit :: k), Tested a)
  => Monoid.Comonoid (a :: TESTED cs k)
  where
  counit = untestOb @a (prim "counit" (Monoid.counit @(Untest a)))
  comult = untestOb @a (prim "comult" (Monoid.comult @(Untest a)))

-- | The monoids of a category that supplies commutative ones are commutative.
instance
  ( HasWitness M.Monoidal cs
  , Testable k
  , M.SymMonoidal k
  , Monoid.Supplies Monoid.CommutativeMonoid k
  , TestOb (M.Unit :: k)
  , Tested a
  )
  => Monoid.CommutativeMonoid (a :: TESTED cs k)

-- | The comonoids of a category that supplies cocommutative ones are cocommutative.
instance
  ( HasWitness M.Monoidal cs
  , Testable k
  , M.SymMonoidal k
  , Monoid.Supplies Monoid.CocommutativeComonoid k
  , TestOb (M.Unit :: k)
  , Tested a
  )
  => Monoid.CocommutativeComonoid (a :: TESTED cs k)

-- | 'Strength.coact' over the tensor of @p@, e.g. the trace of the category the objects stand for.
instance
  (HasWitness M.Monoidal cs, Testable k, M.Monoidal k, Strength.Costrong M.Tensor p, TestOb (M.Unit :: k))
  => Strength.Costrong M.Tensor (TestedP p :: CAT (TESTED cs k))
  where
  coact @a @x @y (TestedP df f) =
    untestOb3 @a @x @y (TestedP (app "coact" df) (Strength.coact @M.Tensor @p @(Untest a) @(Untest x) @(Untest y) f))

-- | Copying and discarding in the category the objects stand for.
instance
  (HasWitness M.Monoidal cs, Testable k, CopyDiscard.CopyDiscard k, TestOb (M.Unit :: k))
  => CopyDiscard.CopyDiscard (TESTED cs k)
  where
  copy @a = untestOb @a (prim "copy" (CopyDiscard.copy @k @(Untest a)))
  discard @a = untestOb @a (prim "discard" (CopyDiscard.discard @k @(Untest a)))

instance (CategoryOf k) => Laws.Labelled (TESTED cs k) where
  label s (TestedArr _ f) = prim s f

-- * The testable-objects profunctor

-- | An element of @p@ between the objects the endpoints stand for, with a description of how it
-- was built, for printing a failing law.
type TestedP :: forall {csj} {csk} {j} {k}. (j +-> k) -> TESTED csj j +-> TESTED csk k
data TestedP p a b where
  TestedP :: (Tested a, Tested b) => Doc -> p (Untest a) (Untest b) -> TestedP p a b

instance (Profunctor p) => Profunctor (TestedP p :: TESTED csj j +-> TESTED csk k) where
  dimap (TestedArr df f) (TestedArr dg g) (TestedP dx x) = TestedP (apps "dimap" [df, dg, dx]) (dimap f g x)
  lmap (TestedArr df f) (TestedP dx x) = TestedP (apps "lmap" [df, dx]) (lmap f x)
  rmap (TestedArr dg g) (TestedP dx x) = TestedP (apps "rmap" [dg, dx]) (rmap g x)
  r \\ TestedP{} = r

instance (Promonad p) => Promonad (TestedP p :: CAT (TESTED cs k)) where
  id @a = untestOb @a (prim "id" id)
  TestedP dy y . TestedP dx x = TestedP (infixrDoc 9 " . " dy dx) (y . x)

-- | The object @p '%' b@, for the interpretation of a 'Representable' @p@.
type RepF :: forall {csj} {j} {k} {o}. (j +-> k) -> TESTED csj j -> o
data family RepF p b

-- | The structure of being closed under the representing functor of @p@, whose objects in 'TESTED'
-- are formed by 'RepF'. Its witness needs the witnesses of the domain @j@ of @p@, @csj@.
type RepresentedBy :: forall {j} {k}. [Kind -> Constraint] -> (j +-> k) -> Kind -> Constraint
class RepresentedBy csj p k'

instance RepresentedBy csj p k'

data instance Witness (RepresentedBy csj (p :: j +-> k)) k' = RepresentedW (Witnesses csj j) (WithTestObRep j p)

instance
  (HasWitness (RepresentedBy csj p) csk, Representable p, Tested (b :: TESTED csj j))
  => Tested (RepF (p :: j +-> k) b :: TESTED csk k)
  where
  type Untest (RepF p b) = p % Untest b
  untestOb r = untestOb @b (withObRep @p @(Untest b) r)
  untestTestOb ws r = case witness @(RepresentedBy csj p) ws of
    RepresentedW wsj f -> untestTestOb @b wsj (f @(Untest b) r)

instance
  (HasWitness (RepresentedBy csj p) csk, Representable p)
  => Representable (TestedP p :: TESTED csj j +-> TESTED csk k)
  where
  type TestedP p % b = RepF p b
  index (TestedP dx x) = TestedArr (app "index" dx) (index x)
  tabulate @b (TestedArr df f) = untestOb @b (TestedP (app "tabulate" df) (tabulate @p @(Untest b) f))
  repMap (TestedArr df f) = TestedArr (app "repMap" df) (repMap @p f)
  repUniv @b = untestOb @b (prim "repUniv" (repUniv @p @(Untest b)))
