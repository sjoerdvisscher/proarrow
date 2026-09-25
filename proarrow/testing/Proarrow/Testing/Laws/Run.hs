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
  , TestedArr (..)

    -- * Describing arrows
  , Doc
  , prim
  , atom
  , app
  , infixlDoc
  , infixrDoc
  ) where

import Data.Kind (Constraint, Type)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (Property, testProperty)
import Prelude hiding (fst, id, snd, (.))

import Proarrow.Category.Instance.Free qualified as Free
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Category.Monoidal.Closed qualified as Exponential
import Proarrow.Category.Monoidal.CompactClosed qualified as CC
import Proarrow.Category.Monoidal.Distributive qualified as Distributive
import Proarrow.Category.Monoidal.StarAutonomous qualified as SA
import Proarrow.Colimit.BinaryCoproduct qualified as BinaryCoproduct
import Proarrow.Colimit.Initial qualified as Initial
import Proarrow.Core (CAT, CategoryOf (..), Kind, Profunctor (..), Promonad (..), dimapDefault)
import Proarrow.Limit.BinaryProduct qualified as BinaryProduct
import Proarrow.Limit.Terminal qualified as Terminal
import Proarrow.Testing
  ( Some (..)
  , Testable (..)
  , WithTestOb2
  , WithTestObCoprod
  , WithTestObDual
  , WithTestObExp
  , WithTestObProd
  , genNamed
  , genOb
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
    gen :: forall (x :: TESTED cs k) y. (Tested x, Tested y) => String -> Property (x ~> y)
    gen s =
      untestTestOb2 @x @y witnesses (prim s <$> genNamed @(Untest x ~> Untest y) s)
    checkLaw :: Laws.Law cs -> Property ()
    checkLaw (Laws.Law lawName body) = do
      Some @a <- genObject
      Some @b <- genObject
      Some @c <- genObject
      Some @d <- genObject
      Some @e <- genObject
      eq <- body @(TLeaf a :: TESTED cs k) @(TLeaf b) @(TLeaf c) @(TLeaf d) @(TLeaf e) gen
      case eq of
        TestedArr @s @t dl l Laws.:=: TestedArr dr r ->
          untestTestOb2 @s @t @(Property ()) witnesses $
            testEq lawName (dl 0 "") l (dr 0 "") r

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
-- built, for printing a failing law.
type TestedArr :: CAT (TESTED cs k)
data TestedArr a b where
  TestedArr :: (Tested a, Tested b) => Doc -> Untest a ~> Untest b -> TestedArr a b

-- | A description that can be shown at a precedence, like 'showsPrec'.
type Doc = Int -> ShowS

-- | A name, which never needs parentheses.
atom :: String -> Doc
atom s _ = showString s

-- | An arrow described by its name.
prim :: (Tested a, Tested b) => String -> Untest a ~> Untest b -> TestedArr a b
prim s = TestedArr (atom s)

-- | A function applied to one argument.
app :: String -> Doc -> Doc
app f x d = showParen (d > 10) (showString f . showChar ' ' . x 11)

-- | A left or right associative infix operator at the given precedence, like @infixl@ and
-- @infixr@. The operator string includes its surrounding spaces, e.g. @" . "@.
infixlDoc, infixrDoc :: Int -> String -> Doc -> Doc -> Doc
infixlDoc p op x y d = showParen (d > p) (x p . showString op . y (p + 1))
infixrDoc p op x y d = showParen (d > p) (x (p + 1) . showString op . y p)

instance (CategoryOf k) => Profunctor (TestedArr :: CAT (TESTED cs k)) where
  dimap = dimapDefault
  r \\ TestedArr{} = r
instance (CategoryOf k) => Promonad (TestedArr :: CAT (TESTED cs k)) where
  id @a = untestOb @a (prim "id" id)
  TestedArr df f . TestedArr dg g = TestedArr (infixrDoc 9 " . " df dg) (f . g)
instance (CategoryOf k) => CategoryOf (TESTED cs k) where
  type (~>) = TestedArr
  type Ob a = Tested a

instance
  (HasWitness M.Monoidal cs, Testable k, M.Monoidal k, TestOb (M.Unit :: k))
  => M.MonoidalProfunctor (TestedArr :: CAT (TESTED cs k))
  where
  one = prim "one" M.one
  TestedArr df f ** TestedArr dg g = TestedArr (infixlDoc 8 " ** " df dg) (f M.** g)
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

instance (CategoryOf k) => Laws.Labelled (TESTED cs k) where
  label s (TestedArr _ f) = prim s f
