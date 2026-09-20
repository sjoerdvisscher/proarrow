{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}

-- | Star-autonomous categories: symmetric closed categories with a dualizing functor 'Dual', where
-- morphisms @a ** b ~> Dual c@ correspond to @a ~> Dual (b ** c)@ ('linDist'). This gives
-- double-negation elimination ('doubleNeg') and an internal hom @'ExpSA' a b = 'Dual' (a ** Dual b)@
-- -- the categorical semantics of multiplicative linear logic.
module Proarrow.Category.Monoidal.StarAutonomous where

import Prelude qualified as P

import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..), Not)
import Proarrow.Category.Instance.Free
  ( Elem (..)
  , Elems
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
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..), swap, type (**!))
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.Strictified (Strictified (..))
import Proarrow.Core (CAT, CategoryOf (..), Obj, Profunctor (..), Promonad (..), obj)
import Proarrow.Optic (PIso, iso)

-- | A *-autonomous category: a symmetric monoidal closed category with a dualizing object, so
-- that 'Dual' is a contravariant involution and @Hom(a '**' b, 'Dual' c)@ is symmetric in its three
-- arguments.
--
-- __Laws:__
--
-- * 'dual' is a contravariant functor: @'dual' 'id' = 'id'@ and @'dual' (f . g) = 'dual' g . 'dual' f@
-- * 'dual' and 'dualInv' are mutually inverse bijections on hom-sets:
--   @'dualInv' ('dual' f) = f@ and @'dual' ('dualInv' g) = g@
-- * 'linDist' and 'linDistInv' are mutually inverse, giving
--   @Hom(a '**' b, 'Dual' c) ≅ Hom(a, 'Dual' (b '**' c))@, natural in all three variables
-- * 'Proarrow.Category.Monoidal.StarAutonomous.doubleNegIso' witnesses
--   @'Dual' ('Dual' a) ≅ a@, naturally.
--
-- Checked by @Proarrow.Testing.Laws.testStarAutonomous@.
class (SymMonoidal k, Closed k, Ob (Unit :: k)) => StarAutonomous k where
  -- | The dual of an object.
  type Dual (a :: k) :: k

  -- | Recovers @'Ob' ('Dual' a)@ from the objecthood of @a@.
  withObDual :: (Ob (a :: k)) => ((Ob (Dual a)) => r) -> r

  -- | 'Dual'\'s contravariant action on arrows.
  dual :: (a :: k) ~> b -> Dual b ~> Dual a

  -- | Inverse to 'dual' on hom-sets: recovers the undualized arrow.
  dualInv :: (Ob (a :: k), Ob b) => Dual a ~> Dual b -> b ~> a

  -- | Linear distribution: transposes a tensor factor across the dual.
  linDist :: (Ob (a :: k), Ob b, Ob c) => a ** b ~> Dual c -> a ~> Dual (b ** c)

  -- | Inverse to 'linDist'.
  linDistInv :: (Ob (a :: k), Ob b, Ob c) => a ~> Dual (b ** c) -> a ** b ~> Dual c

dualObj :: forall {k} (a :: k). (StarAutonomous k, Ob a) => Obj (Dual a)
dualObj = dual (obj @a)

doubleNeg :: forall {k} (a :: k). (StarAutonomous k, Ob a) => Dual (Dual a) ~> a
doubleNeg = dualInv @k @a (doubleNegInv @(Dual a)) \\ dualObj @(Dual a) \\ dualObj @a

doubleNegInv :: forall {k} (a :: k). (StarAutonomous k, Ob a) => a ~> Dual (Dual a)
doubleNegInv =
  linDistInv @k @Unit @a @(Dual a) (dual (swap @k @a @(Dual a)) . dualityUnitSA @a) . leftUnitorInv @k @a
    \\ dualObj @a

doubleNegIso
  :: forall {k} (a :: k) (a' :: k). (StarAutonomous k, Ob a, Ob a') => PIso a a' (Dual (Dual a)) (Dual (Dual a'))
doubleNegIso = iso doubleNegInv doubleNeg

linDistS
  :: forall {k} (a :: k) (b :: k) c. (StarAutonomous k, Ob c) => '[a, b] ~> '[Dual c] -> '[a] ~> '[Dual (b ** c)]
linDistS f@Str{} = withOb2 @k @b @c (withObDual @k @(b ** c) (Str (linDist @k @a @b @c (unStr f))))

linDistInvS
  :: forall {k} (a :: k) (b :: k) c. (StarAutonomous k, Ob b, Ob c) => '[a] ~> '[Dual (b ** c)] -> '[a, b] ~> '[Dual c]
linDistInvS f@Str{} = withObDual @k @c (Str (linDistInv @k @a @b @c (unStr f)))

type ExpSA a b = Dual (a ** Dual b)

currySA :: forall {k} (a :: k) b c. (StarAutonomous k, Ob a, Ob b) => a ** b ~> c -> a ~> ExpSA b c
currySA f = linDist @k @a @b @(Dual c) (doubleNegInv @c . f) \\ f \\ dual f

applySA :: forall {k} (b :: k) c. (StarAutonomous k, Ob b, Ob c) => ExpSA b c ** b ~> c
applySA =
  doubleNeg @c . withOb2 @k @b @(Dual c) (linDistInv @k @(ExpSA b c) @b @(Dual c) id \\ dualObj @(b ** Dual c))
    \\ dualObj @c

expSA :: forall {k} (a :: k) b x y. (StarAutonomous k) => b ~> y -> x ~> a -> ExpSA a b ~> ExpSA x y
expSA f g = dual (g ** dual f)

dualityUnitSA :: forall {k} (a :: k). (StarAutonomous k, Ob a) => Unit ~> Dual (Dual a ** a)
dualityUnitSA = linDist @k @_ @(Dual a) @a leftUnitor \\ dualObj @a

dualityCounitSA :: forall {k} (a :: k). (StarAutonomous k, Ob a) => Dual a ** a ~> Dual Unit
dualityCounitSA = linDistInv @k @(Dual a) @a @Unit (dual (rightUnitor @k @a)) \\ dualObj @a

instance StarAutonomous () where
  type Dual '() = '()
  withObDual r = r
  dual U.Unit = U.Unit
  dualInv U.Unit = U.Unit
  linDist U.Unit = U.Unit
  linDistInv U.Unit = U.Unit

instance StarAutonomous BOOL where
  type Dual (a :: BOOL) = Not a
  withObDual r = r
  dual Fls = Tru
  dual F2T = F2T
  dual Tru = Fls
  dualInv @a @b f = case (obj @a, obj @b, f) of
    (Fls, Fls, Tru) -> Fls
    (Tru, Fls, F2T) -> F2T
    (Tru, Tru, Fls) -> Tru
    (Fls, Tru, f') -> case f' of {}
  linDist @a @b f = case (obj @a, obj @b) of
    (Fls, Fls) -> F2T
    (Tru, Fls) -> Tru
    (_, Tru) -> f
  linDistInv @_ @b @c f = case (obj @b, obj @c) of
    (Fls, Fls) -> F2T
    (Fls, Tru) -> Fls
    (Tru, _) -> f

-- BOOL is not CompactClosed

instance (StarAutonomous j, StarAutonomous k) => StarAutonomous (j, k) where
  type Dual '(a, b) = '(Dual a, Dual b)
  withObDual @'(a, b) r = withObDual @j @a (withObDual @k @b r)
  dual (f :**: g) = dual f :**: dual g
  dualInv (f :**: g) = dualInv f :**: dualInv g
  linDist @'(a1, a2) @'(b1, b2) @'(c1, c2) (f :**: g) = linDist @j @a1 @b1 @c1 f :**: linDist @k @a2 @b2 @c2 g
  linDistInv @'(a1, a2) @'(b1, b2) @'(c1, c2) (f :**: g) = linDistInv @j @a1 @b1 @c1 f :**: linDistInv @k @a2 @b2 @c2 g

data family DualF (a :: k) :: k
instance (IsFreeOb (a :: FREE cs p), StarAutonomous `Elem` cs) => IsFreeOb (DualF a) where
  type Lower f (DualF a) = Dual (Lower f a)
  lowerOb @k' @f r = fromAll @StarAutonomous @cs @k' (withLowerOb @f @a (withObDual @k' @(Lower f a) r))
instance
  ('[Monoidal, SymMonoidal, Closed, StarAutonomous] `Elems` cs)
  => HasStructure cs (p :: CAT k) StarAutonomous
  where
  data Struct StarAutonomous a b where
    Dual :: a ~> b -> Struct StarAutonomous (DualF b) (DualF a)
    DualInv :: (Ob a, Ob b) => DualF a ~> DualF b -> Struct StarAutonomous b a
    LinDist :: (Ob a, Ob b, Ob c) => a **! b ~> DualF c -> Struct StarAutonomous a (DualF (b **! c))
    LinDistInv :: (Ob a, Ob b, Ob c) => a ~> DualF (b **! c) -> Struct StarAutonomous (a **! b) (DualF c)
  foldStructure go (Dual f) = dual (go f)
  foldStructure @f go (DualInv @a @b g) =
    withLowerOb @f @a (withLowerOb @f @b (dualInv @_ @(Lower f a) @(Lower f b) (go g)))
  foldStructure @f go (LinDist @a @b @c g) =
    withLowerOb @f @a (withLowerOb @f @b (withLowerOb @f @c (linDist @_ @(Lower f a) @(Lower f b) @(Lower f c) (go g))))
  foldStructure @f go (LinDistInv @a @b @c g) =
    withLowerOb @f @a (withLowerOb @f @b (withLowerOb @f @c (linDistInv @_ @(Lower f a) @(Lower f b) @(Lower f c) (go g))))
instance (WithShow a) => P.Show (Struct StarAutonomous a b) where
  showsPrec d (Dual f) = P.showParen (d P.> 10) P.$ P.showString "dual " . P.showsPrec 11 f
  showsPrec d (DualInv f) = P.showParen (d P.> 10) P.$ P.showString "dualInv " . P.showsPrec 11 f
  showsPrec d (LinDist f) = P.showParen (d P.> 10) P.$ P.showString "linDist " . P.showsPrec 11 f
  showsPrec d (LinDistInv f) = P.showParen (d P.> 10) P.$ P.showString "linDistInv " . P.showsPrec 11 f

instance
  ('[Monoidal, SymMonoidal, Closed, StarAutonomous] `Elems` cs)
  => StarAutonomous (FREE cs (p :: CAT k))
  where
  type Dual a = DualF a
  withObDual r = r
  dual f = St (Dual f) Nil \\ f
  dualInv @a @b f = St (DualInv @a @b f) Nil \\ f
  linDist @a @b @c f = St (LinDist @a @b @c f) Nil \\ f
  linDistInv @a @b @c f = St (LinDistInv @a @b @c f) Nil \\ f
