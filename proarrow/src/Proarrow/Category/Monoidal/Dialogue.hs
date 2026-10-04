{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Dialogue categories (Melliès): symmetric monoidal categories with a tensorial negation 'Dual',
-- where morphisms @a ** b ~> Dual c@ correspond to @a ~> Dual (b ** c)@ ('linDist'). Unlike in a
-- *-autonomous category, double negation @'Dual' ('Dual' a) ~> a@ need not exist: only its inverse
-- 'doubleNegInv' does, which 'tripleNeg' undoes on a dual. Any closed category with a chosen
-- answer object is one, with @'Dual' a = a ~~> r@, which is why the continuation passing
-- reading of System L in "Proarrow.Tools.SMC" needs no more than this.
--
-- The *-autonomous categories of "Proarrow.Category.Monoidal.StarAutonomous" are the dialogue
-- categories whose double negation is an isomorphism.
module Proarrow.Category.Monoidal.Dialogue where

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
import Proarrow.Category.Monoidal.Strictified (Strictified (..), obj1, singleton)
import Proarrow.Core (CAT, CategoryOf (..), Kind, Obj, Profunctor (..), Promonad (..), obj)
import Proarrow.Limit.BinaryProduct ()
import Proarrow.Tools.Laws (Bijection (..), Law (..), Laws (..), bijection, (===))

-- | A dialogue category: a symmetric monoidal category with a tensorial negation, so that 'Dual'
-- is a contravariant functor and @Hom(a '**' b, 'Dual' c) ≅ Hom(a, 'Dual' (b '**' c))@.
--
-- __Laws:__
--
-- * 'dual' is a contravariant functor: @'dual' 'id' = 'id'@ and @'dual' (f . g) = 'dual' g . 'dual' f@
-- * 'linDist' and 'linDistInv' are mutually inverse, giving
--   @Hom(a '**' b, 'Dual' c) ≅ Hom(a, 'Dual' (b '**' c))@, natural in all three variables
-- * 'doubleNegInv' is 'doubleNegInvDefault', the one the rest of the structure gives
--
-- Stated as code by the 'Proarrow.Tools.Laws.Laws' instance for 'DialogueStructures', and
-- checked by @Proarrow.Testing.Laws.testDialogue@.
class (SymMonoidal k) => Dialogue k where
  -- | The dual of an object.
  type Dual (a :: k) :: k

  -- | Recovers @'Ob' ('Dual' a)@ from the objecthood of @a@.
  withObDual :: (Ob (a :: k)) => ((Ob (Dual a)) => r) -> r

  -- | 'Dual'\'s contravariant action on arrows.
  dual :: (a :: k) ~> b -> Dual b ~> Dual a

  -- | Linear distribution: transposes a tensor factor across the dual.
  linDist :: (Ob (a :: k), Ob b, Ob c) => a ** b ~> Dual c -> a ~> Dual (b ** c)

  -- | Inverse to 'linDist'.
  linDistInv :: (Ob (a :: k), Ob b, Ob c) => a ~> Dual (b ** c) -> a ** b ~> Dual c

  -- | Double-negation introduction. Defaults to 'doubleNegInvDefault'.
  doubleNegInv :: (Ob (a :: k)) => a ~> Dual (Dual a)
  doubleNegInv @a = doubleNegInvDefault @a

dualObj :: forall {k} (a :: k). (Dialogue k, Ob a) => Obj (Dual a)
dualObj = dual (obj @a)

-- | 'doubleNegInv' from the rest of the structure, through 'linDistInv' and the duality unit.
doubleNegInvDefault :: forall {k} (a :: k). (Dialogue k, Ob a) => a ~> Dual (Dual a)
doubleNegInvDefault =
  linDistInv @k @Unit @a @(Dual a) (dual (swap @k @a @(Dual a)) . dualityUnitSA @a) . leftUnitorInv @k @a
    \\ dualObj @a

-- | Triple negation elimination: a dual is a retract of its double negation, with 'doubleNegInv' as
-- the section, @'tripleNeg' . 'doubleNegInv' = 'id'@. For the computations of "Proarrow.Tools.SMC"
-- it runs a computation of a computation into one, like @join@. It is an isomorphism only in a
-- *-autonomous category: in 'Data.Kind.Type' with answer object 'Prelude.Bool', @Dual ()@ has two
-- elements and @Dual (Dual (Dual ()))@ sixteen.
tripleNeg :: forall {k} (a :: k). (Dialogue k, Ob a) => Dual (Dual (Dual a)) ~> Dual a
tripleNeg = dual (doubleNegInv @k @a)

-- | The Kleisli extension of the double negation monad at a dual: a morphism out of @a@ into a dual,
-- extended to double negations of @a@. This is the bind of the continuation reading of System L in
-- "Proarrow.Tools.SMC". It moves @a@ to the other side of the hom, @g ** y ~> Dual a@, and dualizes.
{-# INLINE bindDual #-}
bindDual
  :: forall {k} (g :: k) a y
   . (Dialogue k, Ob g, Ob a, Ob y)
  => g ** a ~> Dual y
  -> Dual (Dual a) ** g ~> Dual y
bindDual f =
  withObDual @k @a $
    withObDual @k @(Dual a) $
      linDistInv @k @(Dual (Dual a)) @g @y $
        dual $
          linDistInv @k @g @y @a (dual (swap @k @y @a) . linDist @k @g @a @y f)

linDistS
  :: forall {k} (a :: k) (b :: k) c. (Dialogue k, Ob c) => '[a, b] ~> '[Dual c] -> '[a] ~> '[Dual (b ** c)]
linDistS f@Str{} = singleton (linDist @k @a @b @c (unStr f))

linDistInvS
  :: forall {k} (a :: k) (b :: k) c. (Dialogue k, Ob b, Ob c) => '[a] ~> '[Dual (b ** c)] -> '[a, b] ~> '[Dual c]
linDistInvS f@Str{} = withObDual @k @c (Str (linDistInv @k @a @b @c (unStr f)) \\ obj1 @(Dual c))

-- | Par, the dual of the tensor of the duals.
type Par :: forall {k}. k -> k -> k
type Par a b = Dual (Dual a ** Dual b)

-- | Recovers @'Ob' ('Par' a b)@, and the objecthood of the duals it is made of, from the objecthood
-- of @a@ and @b@.
withObPar
  :: forall {k} (a :: k) b r. (Dialogue k, Ob a, Ob b) => ((Ob (Dual a), Ob (Dual b), Ob (Par a b)) => r) -> r
withObPar r = withObDual @k @a (withObDual @k @b (withOb2 @k @(Dual a) @(Dual b) (withObDual @k @(Dual a ** Dual b) r)))

-- | 'Par'\'s action on arrows.
par :: forall {k} (a :: k) b c d. (Dialogue k) => a ~> c -> b ~> d -> Par a b ~> Par c d
par f g = dual (dual f ** dual g)

-- | The symmetry of 'Par'.
parSwap :: forall {k} (a :: k) b. (Dialogue k, Ob a, Ob b) => Par a b ~> Par b a
parSwap = withObPar @a @b (dual (swap @k @(Dual b) @(Dual a)))

-- | Linear distributivity: the tensor distributes into the left of a 'Par'. Given the dual of
-- @a '**' b@, the @a@ turns it into the dual of @b@, which the 'Par' answers with @c@.
weakDistL :: forall {k} (a :: k) b c. (Dialogue k, Ob a, Ob b, Ob c) => a ** Par b c ~> Par (a ** b) c
weakDistL =
  withObPar @b @c
    ( withOb2 @k @a @b
        ( withObDual @k @(a ** b)
            ( withOb2 @k @a @(Par b c)
                ( linDist @k @(a ** Par b c) @(Dual (a ** b)) @(Dual c)
                    ( linDistInv @k @(Par b c) @(Dual b) @(Dual c) id
                        . (obj @(Par b c) ** linDistInv @k @(Dual (a ** b)) @a @b id)
                        . (obj @(Par b c) ** swap @k @a @(Dual (a ** b)))
                        . associator @k @(Par b c) @a @(Dual (a ** b))
                        . (swap @k @a @(Par b c) ** obj @(Dual (a ** b)))
                    )
                )
            )
        )
    )

-- | Linear distributivity on the other side, from 'weakDistL' by symmetry.
weakDistR :: forall {k} (a :: k) b c. (Dialogue k, Ob a, Ob b, Ob c) => Par a b ** c ~> Par a (b ** c)
weakDistR =
  withObPar @b @a
    ( withOb2 @k @c @b
        ( par (obj @a) (swap @k @c @b)
            . parSwap @(c ** b) @a
            . weakDistL @c @b @a
            . swap @k @(Par b a) @c
            . (parSwap @a @b ** obj @c)
        )
    )

dualityUnitSA :: forall {k} (a :: k). (Dialogue k, Ob a) => Unit ~> Dual (Dual a ** a)
dualityUnitSA = linDist @k @_ @(Dual a) @a leftUnitor \\ dualObj @a

dualityCounitSA :: forall {k} (a :: k). (Dialogue k, Ob a) => Dual a ** a ~> Dual Unit
dualityCounitSA = linDistInv @k @(Dual a) @a @Unit (dual (rightUnitor @k @a)) \\ dualObj @a

instance Dialogue () where
  type Dual '() = '()
  withObDual r = r
  dual U.Unit = U.Unit
  linDist U.Unit = U.Unit
  linDistInv U.Unit = U.Unit
  doubleNegInv = U.Unit

instance Dialogue BOOL where
  type Dual (a :: BOOL) = Not a
  withObDual r = r
  dual Fls = Tru
  dual F2T = F2T
  dual Tru = Fls
  linDist @a @b f = case (obj @a, obj @b) of
    (Fls, Fls) -> F2T
    (Tru, Fls) -> Tru
    (_, Tru) -> f
  linDistInv @_ @b @c f = case (obj @b, obj @c) of
    (Fls, Fls) -> F2T
    (Fls, Tru) -> Fls
    (Tru, _) -> f
  doubleNegInv @a = case obj @a of Fls -> Fls; Tru -> Tru

instance (Dialogue j, Dialogue k) => Dialogue (j, k) where
  type Dual '(a, b) = '(Dual a, Dual b)
  withObDual @'(a, b) r = withObDual @j @a (withObDual @k @b r)
  dual (f :**: g) = dual f :**: dual g
  linDist @'(a1, a2) @'(b1, b2) @'(c1, c2) (f :**: g) = linDist @j @a1 @b1 @c1 f :**: linDist @k @a2 @b2 @c2 g
  linDistInv @'(a1, a2) @'(b1, b2) @'(c1, c2) (f :**: g) = linDistInv @j @a1 @b1 @c1 f :**: linDistInv @k @a2 @b2 @c2 g
  doubleNegInv @'(a, b) = doubleNegInv @j @a :**: doubleNegInv @k @b

data family DualF (a :: k) :: k
instance (IsFreeOb (a :: FREE cs p), Dialogue `Elem` cs) => IsFreeOb (DualF a) where
  type Lower f (DualF a) = Dual (Lower f a)
  lowerOb @k' @f r = fromAll @Dialogue @cs @k' (withLowerOb @f @a (withObDual @k' @(Lower f a) r))

-- | The structures the free category needs for 'Dialogue', and those its laws are stated for.
type DialogueStructures :: [Kind -> Constraint]
type DialogueStructures = '[Monoidal, SymMonoidal, Dialogue]

instance
  (DialogueStructures `Elems` cs)
  => HasStructure cs (p :: CAT k) Dialogue
  where
  data Struct Dialogue a b where
    Dual :: a ~> b -> Struct Dialogue (DualF b) (DualF a)
    LinDist :: (Ob a, Ob b, Ob c) => a **! b ~> DualF c -> Struct Dialogue a (DualF (b **! c))
    LinDistInv :: (Ob a, Ob b, Ob c) => a ~> DualF (b **! c) -> Struct Dialogue (a **! b) (DualF c)
  foldStructure go (Dual f) = dual (go f)
  foldStructure @f go (LinDist @a @b @c g) =
    withLowerOb @f @a (withLowerOb @f @b (withLowerOb @f @c (linDist @_ @(Lower f a) @(Lower f b) @(Lower f c) (go g))))
  foldStructure @f go (LinDistInv @a @b @c g) =
    withLowerOb @f @a (withLowerOb @f @b (withLowerOb @f @c (linDistInv @_ @(Lower f a) @(Lower f b) @(Lower f c) (go g))))
instance (WithShow a) => P.Show (Struct Dialogue a b) where
  showsPrec d (Dual f) = P.showParen (d P.> 10) P.$ P.showString "dual " . P.showsPrec 11 f
  showsPrec d (LinDist f) = P.showParen (d P.> 10) P.$ P.showString "linDist " . P.showsPrec 11 f
  showsPrec d (LinDistInv f) = P.showParen (d P.> 10) P.$ P.showString "linDistInv " . P.showsPrec 11 f

instance
  (DialogueStructures `Elems` cs)
  => Dialogue (FREE cs (p :: CAT k))
  where
  type Dual a = DualF a
  withObDual r = r
  dual f = St (Dual f) Nil \\ f
  linDist @a @b @c f = St (LinDist @a @b @c f) Nil \\ f
  linDistInv @a @b @c f = St (LinDistInv @a @b @c f) Nil \\ f

-- | 'dual' is a contravariant functor, 'linDist' is a natural bijection
-- @Hom(a ** b, Dual c) ≅ Hom(a, Dual (b ** c))@ with inverse 'linDistInv', and 'doubleNegInv' is
-- the one they give.
instance Laws DialogueStructures where
  laws =
    [ Law "dual identity" \ @a _ -> withObDual @_ @a (dual (obj @a) === id)
    , Law "dual composition" \ @a @b @c mor -> do
        f <- mor @a @b "f"
        g <- mor @b @c "g"
        dual (g . f) === dual f . dual g
    , Law "linDist naturality" \ @a @b @c @d @e mor ->
        withOb2 @_ @a @b $ withOb2 @_ @d @e $ withObDual @_ @c $ withObDual @_ @d do
          p <- mor @(a ** b) @(Dual c) "p"
          f <- mor @d @a "f"
          g <- mor @e @b "g"
          h <- mor @d @c "h"
          linDist @_ @d @e @d (dual h . p . (f ** g)) === dual (g ** h) . linDist @_ @a @b @c p . f
    ]
      P.++ bijection
        "linDist"
        ( \ @a @b @c mor ->
            withOb2 @_ @a @b $
              withOb2 @_ @b @c $
                withObDual @_ @c $
                  withObDual @_ @(b ** c) $
                    Bijection (mor @(a ** b) @(Dual c) "p") (mor @a @(Dual (b ** c)) "q") (linDist @_ @a @b @c) (linDistInv @_ @a @b @c)
        )
      P.++ [ Law "doubleNegInv definition" \ @a _ -> withObDual @_ @a $ withObDual @_ @(Dual a) (doubleNegInv @_ @a === doubleNegInvDefault @a)
           ]
