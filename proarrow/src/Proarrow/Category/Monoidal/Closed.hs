{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Closed monoidal categories: 'Closed' provides the internal hom @a '~~>' b@, right adjoint to
-- tensoring, with 'curry', 'apply' and functoriality @('^^^')@. Also defines cartesian closed
-- ('CCC') and bicartesian closed ('BiCCC') categories.
module Proarrow.Category.Monoidal.Closed where

import Data.Kind (Type)
import Prelude (($))
import Prelude qualified as P

import Proarrow.Category.Instance.Bool (BOOL (..), BoolLeq, Booleans (..))
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
import Proarrow.Category.Instance.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..), type (**!))
import Proarrow.Category.Monoidal.Strictified (Fold, Strictified (..), concatMany, obj1, singleton, splitMany, (==))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), obj, (//), type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Limit.BinaryProduct ()
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Representable (Rep (..))

infixr 2 ~~>

-- | A (right) closed monoidal category: every @b '~~>' c@ is an internal hom, right adjoint to
-- tensoring with @b@. 'curry' and 'Proarrow.Category.Monoidal.Closed.uncurry' witness the
-- adjunction @Hom(a '**' b, c) ≅ Hom(a, b '~~>' c)@.
--
-- __Laws:__
--
-- * @'curry'@ and @'Proarrow.Category.Monoidal.Closed.uncurry'@ are mutually inverse:
--   @'Proarrow.Category.Monoidal.Closed.uncurry' ('curry' f) = f@ and
--   @'curry' ('Proarrow.Category.Monoidal.Closed.uncurry' g) = g@
-- * and natural in all three variables: for @f :: a' '~>' a@, @g :: b' '~>' b@, @h :: c '~>' c'@,
--   @'curry' . 'dimap' (f '**' g) h = 'dimap' f (h '^^^' g) . 'curry'@
--
-- Together these say @'curry'@ is a natural isomorphism, which also forces the familiar
-- @'apply' . ('curry' f '**' 'id') = f@. The exponential is thereby functorial: @'(^^^)'@ is
-- contravariant in its second argument and covariant in its first.
--
-- Checked by @Proarrow.Testing.Laws.propClosed@.
class (Monoidal k) => Closed k where
  -- | The internal hom (exponential) object.
  type (a :: k) ~~> (b :: k) :: k

  -- | Recovers @'Ob' (a '~~>' b)@ from the objecthood of the ends.
  withObExp :: (Ob (a :: k), Ob b) => ((Ob (a ~~> b)) => r) -> r

  -- | Transposes an arrow out of a tensor into one into an exponential.
  curry :: (Ob (a :: k), Ob b) => a ** b ~> c -> a ~> b ~~> c

  -- | Evaluation: the counit of the adjunction.
  apply :: (Ob (a :: k), Ob b) => (a ~~> b) ** a ~> b

  -- | The exponential's action on arrows: covariant in the result, contravariant in the argument.
  (^^^) :: forall (a :: k) b x y. b ~> y -> x ~> a -> a ~~> b ~> x ~~> y
  f ^^^ g =
    f //
      g //
        withObExp @k @a @b $
          let ab = obj @(a ~~> b) in curry @k @(a ~~> b) @x (f . apply @k @a @b . (ab ** g))

uncurry :: forall {k} b c (a :: k). (Closed k) => (Ob b, Ob c) => a ~> b ~~> c -> a ** b ~> c
uncurry f = apply @k @b @c . (f ** obj @b)

curryS :: forall {k} b c (a :: k). (Closed k) => [a, b] ~> '[c] -> '[a] ~> '[b ~~> c]
curryS (Str f) = withObExp @k @b @c $ Str (curry @k @a @b @c f)

curryS'
  :: forall {k} as c (b :: k). (Closed k, Ob as, Ob b) => (as ** '[b]) ~> '[c] -> as ~> '[b ~~> c]
curryS' f = concatMany == curryS @b @c @(Fold as) (splitMany @as ** obj1 == f)

applyS :: forall {k} (a :: k) b. (Closed k, Ob a, Ob b) => '[a ~~> b, a] ~> '[b]
applyS = withObExp @k @a @b $ Str (apply @k @a @b)

uncurryS :: forall {k} b c (a :: k). (Closed k, Ob b, Ob c) => '[a] ~> '[b ~~> c] -> '[a, b] ~> '[c]
uncurryS f = f ** obj1 == applyS

uncurryS' :: forall {k} as b (c :: k). (Closed k, Ob b, Ob c) => as ~> '[b ~~> c] -> (as ** '[b]) ~> '[c]
uncurryS' f@Str{} = concatMany @as ** obj1 == uncurryS @b @c @(Fold as) (splitMany == f)

compS :: forall {k} (a :: k) b c. (Closed k, Ob a, Ob b, Ob c) => '[b ~~> c, a ~~> b] ~> '[a ~~> c]
compS =
  withObExp @k @b @c $
    withObExp @k @a @b $
      curryS' (obj1 ** applyS @a @b == applyS @b @c)

comp :: forall {k} (a :: k) b c. (Closed k, Ob a, Ob b, Ob c) => (b ~~> c) ** (a ~~> b) ~> a ~~> c
comp = unStr (compS @a @b @c)

mkExponentialS :: forall {k} (a :: k) b. (Closed k) => '[a] ~> '[b] -> '[] ~> '[a ~~> b]
mkExponentialS f@Str{} = curryS' f

mkExponential :: forall {k} a b. (Closed k) => (a :: k) ~> b -> Unit ~> (a ~~> b)
mkExponential ab = unStr (mkExponentialS (singleton ab))

lowerS :: forall {k} (a :: k) b. (Closed k, Ob a, Ob b) => ('[] ~> '[a ~~> b]) -> '[a] ~> '[b]
lowerS = uncurryS'

lower :: forall {k} (a :: k) b. (Closed k, Ob a, Ob b) => (Unit ~> (a ~~> b)) -> a ~> b
lower f = unStr (lowerS (Str f)) \\ f

toEl :: forall {k} (a :: k). (Closed k, Ob a) => a ~> Unit ~~> a
toEl = curry @k @a @Unit @a rightUnitor

instance Closed Type where
  type a ~~> b = a -> b
  withObExp r = r
  curry = P.curry
  apply = P.uncurry id
  (^^^) = P.flip dimap

instance Closed () where
  type '() ~~> '() = '()
  withObExp r = r
  curry U.Unit = U.Unit
  apply = U.Unit
  U.Unit ^^^ U.Unit = U.Unit

-- | Implication is the internal hom of the walking arrow: @a ~~> b@ is @'BoolLeq' a b@.
instance Closed BOOL where
  type a ~~> b = BoolLeq a b
  withObExp @a @b r = case (obj @a, obj @b) of
    (Fls, Fls) -> r
    (Fls, Tru) -> r
    (Tru, Fls) -> r
    (Tru, Tru) -> r
  curry @a @b @c f =
    ( case (obj @a, obj @b, obj @c) of
        (Fls, Fls, Fls) -> F2T
        (Fls, Fls, Tru) -> F2T
        (Fls, Tru, Fls) -> Fls
        (Fls, Tru, Tru) -> F2T
        (Tru, Fls, Fls) -> Tru
        (Tru, Fls, Tru) -> Tru
        (Tru, Tru, Fls) -> case f of {}
        (Tru, Tru, Tru) -> Tru
    )
      \\ f
  apply @a @b = case (obj @a, obj @b) of
    (Fls, Fls) -> Fls
    (Fls, Tru) -> F2T
    (Tru, Fls) -> Fls
    (Tru, Tru) -> Tru

instance (Closed j, Closed k) => Closed (j, k) where
  type '(a1, a2) ~~> '(b1, b2) = '(a1 ~~> b1, a2 ~~> b2)
  withObExp @'(a1, a2) @'(b1, b2) r = withObExp @j @a1 @b1 (withObExp @k @a2 @b2 r)
  curry @'(a1, a2) @'(b1, b2) (f1 :**: f2) = curry @j @a1 @b1 f1 :**: curry @k @a2 @b2 f2
  apply @'(a1, a2) @'(b1, b2) = apply @j @a1 @b1 :**: apply @k @a2 @b2
  (f1 :**: f2) ^^^ (g1 :**: g2) = (f1 ^^^ g1) :**: (f2 ^^^ g2)

data family ExpRep :: (OPPOSITE k, k) +-> k
instance (Closed k) => FunctorForRep (ExpRep :: (OPPOSITE k, k) +-> k) where
  type ExpRep @ '(OP a, b) = a ~~> b
  fmap (Op f :**: g) = g ^^^ f

data family Not (r :: k) :: OPPOSITE k +-> k
instance (Closed k, Ob r) => FunctorForRep (Not (r :: k)) where
  type Not r @ OP a = a ~~> r
  fmap (Op f) = obj @r ^^^ f

-- | The "reader"\/exponential-by-@m@ functor, covariant unlike 'Not' (which fixes the codomain).
data family Exp (m :: k) :: k +-> k

instance (Closed k, Ob m) => FunctorForRep (Exp m :: k +-> k) where
  type Exp m @ a = m ~~> a
  fmap f = f ^^^ obj @m

-- | The Op-Op adjunction, giving rise to the continuation monad.
instance (Closed k, SymMonoidal k, Ob r) => Corepresentable (Rep (Not (r :: k))) where
  type Rep (Not r) %% a = OP (a ~~> r)
  cotabulate (Op f) = Rep (swapClosed @r f) \\ f
  coindex (Rep f) = Op (swapClosed @r f)
  corepMap f = Op (obj @r ^^^ f)

swapClosed :: forall {k} (c :: k) a b. (Closed k, SymMonoidal k, Ob b, Ob c) => a ~> b ~~> c -> b ~> a ~~> c
swapClosed f = curry @k @b @a (uncurry @b @c f . swap @k @b @a) \\ f

data family (-->) (a :: k) (b :: k) :: k
instance (IsFreeOb (a :: FREE cs p), IsFreeOb b, '[Closed, Monoidal] `Elems` cs) => IsFreeOb (a --> b) where
  type Lower f (a --> b) = Lower f a ~~> Lower f b
  lowerOb @k' @f r = fromAll @Closed @cs @k' (withLowerOb @f @a (withLowerOb @f @b (withObExp @k' @(Lower f a) @(Lower f b) r)))
instance ('[Closed, Monoidal] `Elems` cs) => HasStructure cs (p :: CAT k) Closed where
  data Struct Closed a b where
    Apply :: (Ob a, Ob b) => Struct Closed ((a --> b) **! a) b
    Curry :: forall a b c. (Ob a, Ob b) => (a **! b) ~> c -> Struct Closed a (b --> c)
  foldStructure @f _ (Apply @a @b) = withLowerOb @f @a (withLowerOb @f @b (apply @_ @(Lower f a) @(Lower f b)))
  foldStructure @f go (Curry @a @b f) = withLowerOb @f @a (withLowerOb @f @b (curry @_ @(Lower f a) @(Lower f b) (go f)))
instance (WithShow a) => P.Show (Struct Closed a b) where
  showsPrec _ Apply = P.showString "apply"
  showsPrec d (Curry f) = P.showParen (d P.> 10) $ P.showString "curry " . P.showsPrec 11 f

instance ('[Closed, Monoidal] `Elems` cs) => Closed (FREE cs (p :: CAT k)) where
  type a ~~> b = a --> b
  withObExp r = r
  curry f = St (Curry f) Nil \\ f
  apply = St Apply Nil
