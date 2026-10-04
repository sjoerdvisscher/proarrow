{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}

-- | Star-autonomous categories: dialogue categories ("Proarrow.Category.Monoidal.Dialogue") whose
-- dualizing functor 'Dual' is an involution, so that double negation @'Dual' ('Dual' a) ≅ a@
-- ('doubleNeg') and 'dual' is bijective on hom-sets ('dualInv'). They are closed, with an internal
-- hom @'ExpSA' a b = 'Dual' (a ** Dual b)@, and are the categorical semantics of multiplicative
-- linear logic.
module Proarrow.Category.Monoidal.StarAutonomous where

import Data.Kind (Constraint)
import Prelude (($))
import Prelude qualified as P

import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..))
import Proarrow.Category.Instance.Free
  ( Elems
  , FREE (..)
  , Free (..)
  , HasStructure (..)
  , IsFreeOb (..)
  , Lower
  , WithShow
  , withLowerOb
  )
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.Dialogue (Dialogue (..), DualF, dualObj)
import Proarrow.Core (CAT, CategoryOf (..), Kind, Profunctor (..), Promonad (..), obj)
import Proarrow.Optic (PIso, iso)
import Proarrow.Tools.Laws (Bijection (..), Inverses (..), Laws (..), bijection, inverses)

-- | A *-autonomous category: a dialogue category whose dual is an involution, so that
-- @Hom(a '**' b, 'Dual' c)@ is symmetric in its three arguments.
--
-- __Laws:__ those of 'Dialogue', and
--
-- * 'dual' and 'dualInv' are mutually inverse bijections on hom-sets:
--   @'dualInv' ('dual' f) = f@ and @'dual' ('dualInv' g) = g@
-- * 'doubleNeg' and 'doubleNegInv' are mutually inverse, so @'Dual' ('Dual' a) ≅ a@
--
-- Stated as code by the 'Proarrow.Tools.Laws.Laws' instance for 'StarAutonomousStructures', and
-- checked by @Proarrow.Testing.Laws.testStarAutonomous@.
class (Dialogue k, Closed k) => StarAutonomous k where
  -- | Inverse to 'dual' on hom-sets: recovers the undualized arrow.
  dualInv :: (Ob (a :: k), Ob b) => Dual a ~> Dual b -> b ~> a

  -- | Double-negation elimination. Defaults to 'doubleNegDefault'; an instance whose double dual
  -- is the object itself can say so directly.
  doubleNeg :: (Ob (a :: k)) => Dual (Dual a) ~> a
  doubleNeg @a = doubleNegDefault @a

-- | 'doubleNeg' from the rest of the structure: 'dualInv' of 'doubleNegInv' at the dual.
doubleNegDefault :: forall {k} (a :: k). (StarAutonomous k, Ob a) => Dual (Dual a) ~> a
doubleNegDefault = dualInv @k @a (doubleNegInv @k @(Dual a)) \\ dualObj @(Dual a) \\ dualObj @a

doubleNegIso
  :: forall {k} (a :: k) (a' :: k). (StarAutonomous k, Ob a, Ob a') => PIso a a' (Dual (Dual a)) (Dual (Dual a'))
doubleNegIso = iso doubleNegInv doubleNeg

type ExpSA a b = Dual (a ** Dual b)

currySA :: forall {k} (a :: k) b c. (StarAutonomous k, Ob a, Ob b) => a ** b ~> c -> a ~> ExpSA b c
currySA f = linDist @k @a @b @(Dual c) (doubleNegInv @k @c . f) \\ f \\ dual f

applySA :: forall {k} (b :: k) c. (StarAutonomous k, Ob b, Ob c) => ExpSA b c ** b ~> c
applySA =
  doubleNeg @k @c . withOb2 @k @b @(Dual c) (linDistInv @k @(ExpSA b c) @b @(Dual c) id \\ dualObj @(b ** Dual c))
    \\ dualObj @c

expSA :: forall {k} (a :: k) b x y. (StarAutonomous k) => b ~> y -> x ~> a -> ExpSA a b ~> ExpSA x y
expSA f g = dual (g ** dual f)

instance StarAutonomous () where
  dualInv U.Unit = U.Unit
  doubleNeg = U.Unit

instance StarAutonomous BOOL where
  dualInv @a @b f = case (obj @a, obj @b, f) of
    (Fls, Fls, Tru) -> Fls
    (Tru, Fls, F2T) -> F2T
    (Tru, Tru, Fls) -> Tru
    (Fls, Tru, f') -> case f' of {}
  doubleNeg @a = case obj @a of Fls -> Fls; Tru -> Tru

-- BOOL is not CompactClosed

instance (StarAutonomous j, StarAutonomous k) => StarAutonomous (j, k) where
  dualInv (f :**: g) = dualInv f :**: dualInv g
  doubleNeg @'(a, b) = doubleNeg @j @a :**: doubleNeg @k @b

-- | The structures the free category needs for 'StarAutonomous', and those its laws are stated for.
type StarAutonomousStructures :: [Kind -> Constraint]
type StarAutonomousStructures = '[Monoidal, SymMonoidal, Closed, Dialogue, StarAutonomous]

instance
  (StarAutonomousStructures `Elems` cs)
  => HasStructure cs (p :: CAT k) StarAutonomous
  where
  data Struct StarAutonomous a b where
    DualInv :: (Ob a, Ob b) => DualF a ~> DualF b -> Struct StarAutonomous b a
  foldStructure @f go (DualInv @a @b g) =
    withLowerOb @f @a (withLowerOb @f @b (dualInv @_ @(Lower f a) @(Lower f b) (go g)))
instance (WithShow a) => P.Show (Struct StarAutonomous a b) where
  showsPrec d (DualInv f) = P.showParen (d P.> 10) P.$ P.showString "dualInv " . P.showsPrec 11 f

instance
  (StarAutonomousStructures `Elems` cs)
  => StarAutonomous (FREE cs (p :: CAT k))
  where
  dualInv @a @b f = St (DualInv @a @b f) Nil \\ f

-- | 'dual' is bijective on hom-sets with inverse 'dualInv', and 'doubleNeg' is an isomorphism.
-- The rest is in the laws of 'DialogueStructures'.
instance Laws StarAutonomousStructures where
  laws =
    bijection
      "dual"
      ( \ @a @b mor ->
          withObDual @_ @a $
            withObDual @_ @b $
              Bijection (mor @a @b "f") (mor @(Dual b) @(Dual a) "g") dual (dualInv @_ @b @a)
      )
      P.++ inverses "doubleNeg" \ @a -> Inverses (doubleNegInv @_ @a) (doubleNeg @_ @a)
