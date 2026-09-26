{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Law-checking a class of your own with 'testLaws', using only the exports of
-- "Proarrow.Testing.Laws.Run". It also keeps those exports honest: if one this needs goes
-- missing, this module stops compiling.
--
-- The class is a functor on objects, @'Sq' a = (a, a)@ in 'Type'. Checking its laws takes:
--
-- * the laws themselves, a 'Laws' instance for the structure list;
-- * a former for the new kind of object, here 'SqF', with a 'Tested' instance saying what it
--   stands for and how its 'Ob' and 'TestOb' are rebuilt;
-- * a 'Witness' for the structure, saying how 'TestOb' is closed under the former;
-- * the class instance for 'TESTED', whose arrows describe themselves for failure messages.
module Examples.CustomLaws where

import Data.Kind (Constraint, Type)
import Test.Tasty (TestTree)
import Prelude hiding (id, (.))

import Proarrow.Core (CategoryOf (..), Kind, Promonad (..), obj)
import Proarrow.Testing (TestOb)
import Proarrow.Testing.Laws.Run
  ( HasWitness (..)
  , TESTED
  , Tested (..)
  , TestedArr (..)
  , Witness
  , Witnesses (..)
  , app
  , testLaws
  )
import Proarrow.Tools.Laws (Law (..), Laws (..), (=:=))

import Props.Hask ()

-- | A functor on objects, given by a type family.
type HasSquare :: Kind -> Constraint
class (CategoryOf k) => HasSquare k where
  type Sq (a :: k) :: k
  withObSq :: (Ob (a :: k)) => ((Ob (Sq a)) => r) -> r
  sq :: (a :: k) ~> b -> Sq a ~> Sq b

instance HasSquare Type where
  type Sq a = (a, a)
  withObSq r = r
  sq f (x, y) = (f x, f y)

-- | 'sq' preserves identities and composition.
instance Laws '[HasSquare] where
  laws =
    [ Law "sq identity" \ @a _ -> withObSq @_ @a (sq (obj @a) =:= id)
    , Law "sq composition" \ @a @b @c mor -> do
        f <- mor @a @b "f"
        g <- mor @b @c "g"
        sq (g . f) =:= sq g . sq f
    ]

-- | The object former: @'SqF' a@ stands for @'Sq' a@.
data family SqF (a :: k) :: k

newtype instance Witness HasSquare k = SquareW (forall (a :: k) r. (TestOb a) => ((TestOb (Sq a)) => r) -> r)

instance (HasWitness HasSquare cs, HasSquare k, Tested (a :: TESTED cs k)) => Tested (SqF a) where
  type Untest (SqF a) = Sq (Untest a)
  untestOb r = untestOb @a (withObSq @k @(Untest a) r)
  untestTestOb ws r = untestTestOb @a ws (case witness @HasSquare ws of SquareW f -> f @(Untest a) r)

instance (HasWitness HasSquare cs, HasSquare k) => HasSquare (TESTED cs k) where
  type Sq a = SqF a
  withObSq r = r
  sq (TestedArr d f) = TestedArr (app "sq" d) (sq f)

test :: TestTree
test = testLaws @'[HasSquare] "Custom laws" (SquareW (\r -> r) :& WNil :: Witnesses '[HasSquare] Type)
