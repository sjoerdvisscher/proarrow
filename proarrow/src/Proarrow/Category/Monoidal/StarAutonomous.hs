{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}

-- | Star-autonomous categories: symmetric closed categories with a dualizing functor 'Dual', where
-- morphisms @a ** b ~> Dual c@ correspond to @a ~> Dual (b ** c)@ ('linDist'). This gives
-- double-negation elimination ('doubleNeg') and an internal hom @'ExpSA' a b = 'Dual' (a ** Dual b)@
-- Star-autonomous categories are the categorical semantics of multiplicative linear logic.
module Proarrow.Category.Monoidal.StarAutonomous where

import Data.Kind (Constraint)
import Prelude (($))
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
import Proarrow.Core (CAT, CategoryOf (..), Kind, Obj, Profunctor (..), Promonad (..), obj)
import Proarrow.Optic (PIso, iso)
import Proarrow.Tools.Laws
  ( Bijection (..)
  , Inverses (..)
  , Law (..)
  , Laws (..)
  , bijection
  , inverses
  , (=:=)
  )

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
-- * 'doubleNeg' and 'doubleNegInv' are mutually inverse, so @'Dual' ('Dual' a) ≅ a@, and
--   'doubleNegInv' is 'doubleNegInvDefault', the one the rest of the structure gives
--
-- Stated as code by the 'Proarrow.Tools.Laws.Laws' instance for 'StarAutonomousStructures', and
-- checked by @Proarrow.Testing.Laws.testStarAutonomous@.
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

  -- | Double-negation elimination. Defaults to 'doubleNegDefault'; an instance whose double dual
  -- is the object itself can say so directly.
  doubleNeg :: (Ob (a :: k)) => Dual (Dual a) ~> a
  doubleNeg @a = doubleNegDefault @a

  -- | Double-negation introduction, inverse to 'doubleNeg'. Defaults to 'doubleNegInvDefault'.
  doubleNegInv :: (Ob (a :: k)) => a ~> Dual (Dual a)
  doubleNegInv @a = doubleNegInvDefault @a

dualObj :: forall {k} (a :: k). (StarAutonomous k, Ob a) => Obj (Dual a)
dualObj = dual (obj @a)

-- | 'doubleNeg' from the rest of the structure: 'dualInv' of 'doubleNegInv' at the dual.
doubleNegDefault :: forall {k} (a :: k). (StarAutonomous k, Ob a) => Dual (Dual a) ~> a
doubleNegDefault = dualInv @k @a (doubleNegInv @k @(Dual a)) \\ dualObj @(Dual a) \\ dualObj @a

-- | 'doubleNegInv' from the rest of the structure, through 'linDistInv' and the duality unit.
doubleNegInvDefault :: forall {k} (a :: k). (StarAutonomous k, Ob a) => a ~> Dual (Dual a)
doubleNegInvDefault =
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
currySA f = linDist @k @a @b @(Dual c) (doubleNegInv @k @c . f) \\ f \\ dual f

applySA :: forall {k} (b :: k) c. (StarAutonomous k, Ob b, Ob c) => ExpSA b c ** b ~> c
applySA =
  doubleNeg @k @c . withOb2 @k @b @(Dual c) (linDistInv @k @(ExpSA b c) @b @(Dual c) id \\ dualObj @(b ** Dual c))
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
  doubleNeg = U.Unit
  doubleNegInv = U.Unit

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
  doubleNeg @a = case obj @a of Fls -> Fls; Tru -> Tru
  doubleNegInv @a = case obj @a of Fls -> Fls; Tru -> Tru

-- BOOL is not CompactClosed

instance (StarAutonomous j, StarAutonomous k) => StarAutonomous (j, k) where
  type Dual '(a, b) = '(Dual a, Dual b)
  withObDual @'(a, b) r = withObDual @j @a (withObDual @k @b r)
  dual (f :**: g) = dual f :**: dual g
  dualInv (f :**: g) = dualInv f :**: dualInv g
  linDist @'(a1, a2) @'(b1, b2) @'(c1, c2) (f :**: g) = linDist @j @a1 @b1 @c1 f :**: linDist @k @a2 @b2 @c2 g
  linDistInv @'(a1, a2) @'(b1, b2) @'(c1, c2) (f :**: g) = linDistInv @j @a1 @b1 @c1 f :**: linDistInv @k @a2 @b2 @c2 g
  doubleNeg @'(a, b) = doubleNeg @j @a :**: doubleNeg @k @b
  doubleNegInv @'(a, b) = doubleNegInv @j @a :**: doubleNegInv @k @b

data family DualF (a :: k) :: k
instance (IsFreeOb (a :: FREE cs p), StarAutonomous `Elem` cs) => IsFreeOb (DualF a) where
  type Lower f (DualF a) = Dual (Lower f a)
  lowerOb @k' @f r = fromAll @StarAutonomous @cs @k' (withLowerOb @f @a (withObDual @k' @(Lower f a) r))

-- | The structures the free category needs for 'StarAutonomous', and those its laws are stated for.
type StarAutonomousStructures :: [Kind -> Constraint]
type StarAutonomousStructures = '[Monoidal, SymMonoidal, Closed, StarAutonomous]

instance
  (StarAutonomousStructures `Elems` cs)
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
  (StarAutonomousStructures `Elems` cs)
  => StarAutonomous (FREE cs (p :: CAT k))
  where
  type Dual a = DualF a
  withObDual r = r
  dual f = St (Dual f) Nil \\ f
  dualInv @a @b f = St (DualInv @a @b f) Nil \\ f
  linDist @a @b @c f = St (LinDist @a @b @c f) Nil \\ f
  linDistInv @a @b @c f = St (LinDistInv @a @b @c f) Nil \\ f

-- | 'dual' is a contravariant functor, bijective on hom-sets with inverse 'dualInv'; 'doubleNeg'
-- is an isomorphism; and 'linDist' is a natural bijection
-- @Hom(a ** b, Dual c) ≅ Hom(a, Dual (b ** c))@ with inverse 'linDistInv'.
instance Laws StarAutonomousStructures where
  laws =
    [ Law "dual identity" \ @a _ -> withObDual @_ @a (dual (obj @a) =:= id)
    , Law "dual composition" \ @a @b @c mor -> do
        f <- mor @a @b "f"
        g <- mor @b @c "g"
        dual (g . f) =:= dual f . dual g
    , Law "linDist naturality" \ @a @b @c @d @e mor ->
        withOb2 @_ @a @b $ withOb2 @_ @d @e $ withObDual @_ @c $ withObDual @_ @d do
          p <- mor @(a ** b) @(Dual c) "p"
          f <- mor @d @a "f"
          g <- mor @e @b "g"
          h <- mor @d @c "h"
          linDist @_ @d @e @d (dual h . p . (f ** g)) =:= dual (g ** h) . linDist @_ @a @b @c p . f
    ]
      P.++ bijection
        "dual"
        ( \ @a @b mor ->
            withObDual @_ @a $
              withObDual @_ @b $
                Bijection (mor @a @b "f") (mor @(Dual b) @(Dual a) "g") dual (dualInv @_ @b @a)
        )
      P.++ bijection
        "linDist"
        ( \ @a @b @c mor ->
            withOb2 @_ @a @b $
              withOb2 @_ @b @c $
                withObDual @_ @c $
                  withObDual @_ @(b ** c) $
                    Bijection (mor @(a ** b) @(Dual c) "p") (mor @a @(Dual (b ** c)) "q") (linDist @_ @a @b @c) (linDistInv @_ @a @b @c)
        )
      P.++ [ Law "doubleNegInv definition" \ @a _ -> withObDual @_ @a $ withObDual @_ @(Dual a) (doubleNegInv @_ @a =:= doubleNegInvDefault @a)
           ]
      P.++ inverses "doubleNeg" \ @a -> Inverses (doubleNegInv @_ @a) (doubleNeg @_ @a)
