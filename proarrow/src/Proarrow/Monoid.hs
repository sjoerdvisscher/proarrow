{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Monoids and comonoids internal to a monoidal category: a 'Monoid' @m@ has @'mempty' :: 'Unit' '~>' m@
-- and @'mappend' :: m '**' m '~>' m@; dually a 'Comonoid' has 'counit' and 'comult'. Monoids in
-- 'Data.Kind.Type' are the Prelude monoids, and in a cartesian category every object is a comonoid.
module Proarrow.Monoid where

import Data.Kind (Constraint, Type)
import Data.Type.Nat (SNat (..), SNatI, snat)
import Prelude qualified as P

import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..))
import Proarrow.Category.Instance.Free (Elems, FREE, HasStructure (..), Lower, withLowerOb)
import Proarrow.Category.Instance.Free qualified as F
import Proarrow.Category.Instance.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , NFold
  , NFoldS
  , SymMonoidal (..)
  , Tensor
  , UnitF
  , swapInner
  , (**)
  , type (**!)
  )
import Proarrow.Category.Monoidal.Action (Act, ActionAt, CoprodAction, MonoidalAction (..), actHom)
import Proarrow.Category.Monoidal.Closed (Closed (..), Exp)
import Proarrow.Category.Monoidal.Strength (Strong (..))
import Proarrow.Category.Monoidal.Strictified (Strictified (..), obj1)
import Proarrow.Colimit.BinaryCoproduct
  ( COPROD (..)
  , Coprod (..)
  , HasBinaryCoproducts (..)
  , HasBiproducts (..)
  , HasCoproducts
  , codiag
  )
import Proarrow.Colimit.Initial (HasInitialObject (..), HasZeroObject (..))
import Proarrow.Core (CAT, CategoryOf (..), Kind, Promonad (..), obj, (//), type (+->))
import Proarrow.Object (pattern Objs)
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Constant (Constant)
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (Rep (..))

-- | A monoid object in a monoidal category: a unit and an (associative, unital) multiplication
-- for the object @m@. At @k = Type@ (with tensor @(,)@) this is the ordinary 'P.Monoid'.
type Monoid :: forall {k}. k -> Constraint
class (Monoidal k, Ob m) => Monoid (m :: k) where
  mempty :: Unit ~> m
  mappend :: m ** m ~> m

combine :: (Monoid m) => Unit ~> m -> Unit ~> m -> Unit ~> m
combine f g = mappend . (f ** g) . leftUnitorInv

memptyS :: (Monoid m) => '[] ~> '[m]
memptyS = Str mempty

mappendS :: (Monoid m) => '[m, m] ~> '[m]
mappendS = Str mappend

-- | A law-only marker class for monoids whose multiplication commutes:
-- @'mappend' . 'swap' = 'mappend'@.
class (Monoid m, SymMonoidal k) => CommutativeMonoid (m :: k)

instance (P.Monoid m) => Monoid (m :: Type) where
  mempty () = P.mempty
  mappend = P.uncurry (P.<>)
instance CommutativeMonoid ()

instance Monoid TRU where
  mempty = Tru
  mappend = Tru
instance CommutativeMonoid TRU

newtype GenElt x m = GenElt (x ~> m)

instance (Monoid m, Comonoid (x :: k)) => P.Semigroup (GenElt x (m :: k)) where
  GenElt f <> GenElt g = GenElt (mappend . (f ** g) . comult)
instance (Monoid m, Comonoid (x :: k)) => P.Monoid (GenElt x (m :: k)) where
  mempty = GenElt (mempty . counit)

instance (HasCoproducts k, Ob a) => Monoid (COPR (a :: k)) where
  mempty = Coprod initiate
  mappend = Coprod codiag

memptyAct :: forall {m} {c} t (a :: m) (n :: c). (MonoidalAction t, Monoid a, Ob n) => n ~> Act t a n
memptyAct = actHom @t (mempty @a) (obj @n) . unitorInv @t

mappendAct
  :: forall {m} {c} t (a :: m) (n :: c). (MonoidalAction t, Monoid a, Ob n) => Act t a (Act t a n) ~> Act t a n
mappendAct = actHom @t (mappend @a) (obj @n) . multiplicatorInv @t @a @a @n

-- | A comonoid object: an object that can be discarded ('counit') and copied ('comult').
type Comonoid :: forall {k}. k -> Constraint
class (Monoidal k, Ob c) => Comonoid (c :: k) where
  counit :: c ~> Unit
  comult :: c ~> c ** c

-- | A law-only marker for comonoids whose comultiplication cocommutes: @'swap' . 'comult' = 'comult'@.
-- Dual to 'CommutativeMonoid'.
class (Comonoid c, SymMonoidal k) => CocommutativeComonoid (c :: k)

counitS :: (Comonoid c) => '[c] ~> '[]
counitS = Str counit

comultS :: (Comonoid c) => '[c] ~> '[c, c]
comultS = Str comult

-- | A comonoid structure on @c@ carried as a value. @Unit@ and @('**')@ are type families and so
-- cannot head a 'Comonoid' instance, yet the unit is a comonoid and, in a symmetric monoidal
-- category, so is a tensor of comonoids. 'unitComonoid' and 'tensorComonoid' say so at the value
-- level, so that 'Proarrow.Optic.MonoidalLens.withMonLens' can hand back the comonoid of a
-- composite residual (cf. 'Proarrow.Optic.Action.withAlgP', which passes algebras the same way).
type ComonoidOn :: forall {k}. k -> Type
data ComonoidOn (c :: k) = ComonoidOn {counitOn :: c ~> Unit, comultOn :: c ~> c ** c}

-- | The comonoid structure of a 'Comonoid' instance, as a value.
comonoidOn :: forall {k} (c :: k). (Comonoid c) => ComonoidOn c
comonoidOn = ComonoidOn counit comult

-- | The unit is a comonoid, via the unitor.
unitComonoid :: forall {k}. (Monoidal k) => ComonoidOn (Unit :: k)
unitComonoid = ComonoidOn id (leftUnitorInv @k @Unit)

-- | In a symmetric monoidal category the tensor of two comonoids is a comonoid: counit both
-- halves, or comultiply both halves and swap the inner pair.
tensorComonoid :: forall {k} (a :: k) b. (SymMonoidal k) => ComonoidOn a -> ComonoidOn b -> ComonoidOn (a ** b)
tensorComonoid (ComonoidOn ca@Objs ma) (ComonoidOn cb@Objs mb) =
  ComonoidOn (leftUnitor @k @Unit . (ca ** cb)) (swapInner @a @a @b @b . (ma ** mb))

instance Comonoid (a :: Type) where
  counit _ = ()
  comult a = (a, a)
instance CocommutativeComonoid (a :: Type)

instance Comonoid '() where
  counit = id
  comult = id
instance CocommutativeComonoid '()

instance (Ob a) => Comonoid (a :: BOOL) where
  counit = case obj @a of
    Fls -> F2T
    Tru -> Tru
  comult = case obj @a of
    Fls -> Fls
    Tru -> Tru
instance (Ob a) => CocommutativeComonoid (a :: BOOL)

counitAct :: forall {m} {c} t (a :: m) (n :: c). (MonoidalAction t, Comonoid a, Ob n) => Act t a n ~> n
counitAct = unitor @t . actHom @t (counit @a) (obj @n)

comultAct
  :: forall {m} {c} t (a :: m) (n :: c). (MonoidalAction t, Comonoid a, Ob n) => Act t a n ~> Act t a (Act t a n)
comultAct = multiplicator @t @a @a @n . actHom @t (comult @a) (obj @n)

-- | @'Supplies' c k@ says that every object of the category @k@ satisfies the constraint @c@,
-- e.g. @'Supplies' 'Comonoid' k@ for a category in which every object can be copied and discarded.
-- The constraint comes first (at a higher-rank kind) so that a partial application like
-- @'Supplies' 'Comonoid'@ has kind @Kind -> Constraint@ and can appear in a free category's
-- structure list ("Proarrow.Category.Instance.Free"). Instances are necessarily per-@c@ (an
-- instance variable cannot have a higher-rank kind); each follows the shape of the 'Comonoid' one.
type Supplies :: (forall j. j -> Constraint) -> Kind -> Constraint
class (forall (a :: k). (Ob a) => c a) => Supplies c k

instance (forall (a :: k). (Ob a) => Comonoid a) => Supplies Comonoid k

instance (forall (a :: k). (Ob a) => CocommutativeComonoid a) => Supplies CocommutativeComonoid k

instance (forall (a :: k). (Ob a) => Monoid a) => Supplies Monoid k

instance (forall (a :: k). (Ob a) => CommutativeMonoid a) => Supplies CommutativeMonoid k

instance (Comonoid c) => Monoid (OP c) where
  mempty = Op counit
  mappend = Op comult
instance (CocommutativeComonoid c) => CommutativeMonoid (OP c)

instance (Monoid c) => Comonoid (OP c) where
  counit = Op mempty
  comult = Op mappend
instance (CommutativeMonoid c) => CocommutativeComonoid (OP c)

instance (HasZeroObject k, HasBiproducts k, Ob (a :: k), Ob b) => P.Semigroup (Id a b) where
  Id f <> Id g = Id (sum f g)
instance (HasZeroObject k, HasBiproducts k, Ob (a :: k), Ob b) => P.Monoid (Id a b) where
  mempty = Id zero
instance (HasZeroObject k, HasBiproducts k, Ob (a :: k), Ob b) => CommutativeMonoid (Id a b)

instance (Monoidal k, Monoid r) => MonoidalProfunctor (Rep (Constant r) :: k +-> k) where
  one = Rep mempty
  Rep @x l ** Rep @y r = withOb2 @k @x @y (Rep (mappend . (l ** r)))
instance (HasCoproducts k, Ob r) => MonoidalProfunctor (Coprod (Rep (Constant r)) :: COPROD k +-> COPROD k) where
  one = Coprod (Rep initiate)
  Coprod @_ @_ @x (Rep l) ** Coprod @_ @_ @y (Rep r) = withObCoprod @k @x @y (Coprod (Rep (l ||| r)))
instance (Monoidal k, Comonoid r) => MonoidalProfunctor (Corep (Constant r) :: k +-> k) where
  one = Corep counit
  Corep @x l ** Corep @y r = withOb2 @k @x @y (Corep ((l ** r) . comult))

-- | Tensoring with a monoid, @m ** -@, is an applicative functor: the monoid's unit is @pure@ and
-- its multiplication is @<*>@. Rendered on the representable profunctor @'Rep' ('ActionAt' 'Tensor' m)@
-- (legs @a ~> m ** b@) this is a 'Proarrow.Category.Monoidal.Distributive.StrongDistributiveProfunctor',
-- the Writer applicative of the literature. (The 'Constant' instances above are the degenerate
-- case @b = Unit@.)
instance (SymMonoidal k, Monoid (m :: k)) => MonoidalProfunctor (Rep (ActionAt Tensor m) :: k +-> k) where
  one = Rep (memptyAct @Tensor @m @Unit)
  Rep @x2 l ** Rep @y2 r =
    l // r // withOb2 @k @x2 @y2 (Rep ((mappend @m ** obj @(x2 ** y2)) . swapInner @m @x2 @m @y2 . (l ** r)))

instance
  (Monoidal k, HasCoproducts k, Ob (m :: k))
  => MonoidalProfunctor (Coprod (Rep (ActionAt Tensor m)) :: COPROD k +-> COPROD k)
  where
  one = withOb2 @k @m @InitialObject (Coprod (Rep initiate))
  Coprod (Rep @x2 l) ** Coprod (Rep @y2 r) =
    withObCoprod @k @x2 @y2 (Coprod (Rep ((obj @m ** lft @k @x2 @y2) . l ||| (obj @m ** rgt @k @x2 @y2) . r)))
instance (SymMonoidal k, Ob (m :: k)) => Strong Tensor (Rep (ActionAt Tensor m) :: k +-> k) where
  act @a (Rep @y p) =
    p //
      withOb2 @k @a @y (Rep (associator @k @m @a @y . (swap @k @a @m ** obj @y) . associatorInv @k @a @m @y . (obj @a ** p)))
instance (Monoidal k, HasCoproducts k, Monoid (m :: k)) => Strong CoprodAction (Rep (ActionAt Tensor m) :: k +-> k) where
  act @(COPR a) (Rep @y p) =
    p // withObCoprod @k @a @y (Rep ((obj @m ** lft @k @a @y) . memptyAct @Tensor @m @a ||| (obj @m ** rgt @k @a @y) . p))

-- | The exponential by a comonoid, @m ~~> -@, is an applicative functor (the reader applicative):
-- @pure@ discards the argument with the counit and @<*>@ duplicates it with the comultiplication.
-- Rendered on @'Rep' ('Exp' m)@ (legs @a ~> (m ~~> b)@) this is a
-- 'Proarrow.Category.Monoidal.Distributive.StrongDistributiveProfunctor', so a
-- 'Proarrow.Optic.Grate.Grate' is a 'Proarrow.Optic.Kaleidoscope.Kaleidoscope'.
instance (Closed k, SymMonoidal k, Comonoid (m :: k)) => MonoidalProfunctor (Rep (Exp m) :: k +-> k) where
  one = Rep (curry @k @Unit @m (leftUnitor @k @Unit . (obj @Unit ** counit @m)))
  Rep @x2 @_ @x1 l ** Rep @y2 @_ @y1 r =
    l //
      r //
        withOb2 @k @x1 @y1
          ( withOb2 @k @x2 @y2
              ( withObExp @k @m @x2
                  ( withObExp @k @m @y2
                      ( Rep
                          ( curry @k @(x1 ** y1) @m
                              ( (apply @k @m @x2 ** apply @k @m @y2)
                                  . swapInner @(m ~~> x2) @(m ~~> y2) @m @m
                                  . ((l ** r) ** comult @m)
                              )
                          )
                      )
                  )
              )
          )

instance (Closed k, HasCoproducts k, Ob (m :: k)) => MonoidalProfunctor (Coprod (Rep (Exp m)) :: COPROD k +-> COPROD k) where
  one = withObExp @k @m @InitialObject (Coprod (Rep initiate))
  Coprod (Rep @x2 l) ** Coprod (Rep @y2 r) =
    withObCoprod @k @x2 @y2 (Coprod (Rep ((lft @k @x2 @y2 ^^^ obj @m) . l ||| (rgt @k @x2 @y2 ^^^ obj @m) . r)))
instance (Closed k, SymMonoidal k, Ob (m :: k)) => Strong Tensor (Rep (Exp m) :: k +-> k) where
  act @a (Rep @y @_ @x p) =
    p //
      withOb2 @k @a @x
        ( withOb2 @k @a @y
            ( withObExp @k @m @y
                (Rep (curry @k @(a ** x) @m ((obj @a ** apply @k @m @y) . associator @k @a @(m ~~> y) @m . ((obj @a ** p) ** obj @m))))
            )
        )
instance (Closed k, HasCoproducts k, Comonoid (m :: k)) => Strong CoprodAction (Rep (Exp m) :: k +-> k) where
  act @(COPR a) (Rep @y p) =
    p //
      withObCoprod @k @a @y
        ( withObExp @k @m @a
            ( withObExp @k @m @y
                ( Rep
                    ((lft @k @a @y ^^^ obj @m) . curry @k @a @m (rightUnitor @k @a . (obj @a ** counit @m)) ||| (rgt @k @a @y ^^^ obj @m) . p)
                )
            )
        )

-- | The free-category structure for @'Supplies' 'Monoid'@: every object gets formal 'mappend'
-- ('Join') and 'mempty' ('Sprout') generators, interpreted by 'foldStructure' through the
-- target's own supply.
instance ('[Supplies Monoid, Monoidal] `Elems` cs) => HasStructure cs (p :: CAT k) (Supplies Monoid) where
  data Struct (Supplies Monoid) i o where
    Join :: (Ob a) => Struct (Supplies Monoid) (a **! a) a
    Sprout :: (Ob a) => Struct (Supplies Monoid) UnitF a
  foldStructure @f _ (Join @a) = withLowerOb @f @a (mappend @(Lower f a))
  foldStructure @f _ (Sprout @a) = withLowerOb @f @a (mempty @(Lower f a))

instance P.Show (Struct (Supplies Monoid) a b) where
  showsPrec _ Join = P.showString "mappend"
  showsPrec _ Sprout = P.showString "mempty"

-- | The free-category structure for @'Supplies' 'Comonoid'@, dually: formal 'comult' ('Fork') and
-- 'counit' ('Prune') generators for every object.
instance ('[Supplies Comonoid, Monoidal] `Elems` cs) => HasStructure cs (p :: CAT k) (Supplies Comonoid) where
  data Struct (Supplies Comonoid) i o where
    Fork :: (Ob a) => Struct (Supplies Comonoid) a (a **! a)
    Prune :: (Ob a) => Struct (Supplies Comonoid) a UnitF
  foldStructure @f _ (Fork @a) = withLowerOb @f @a (comult @(Lower f a))
  foldStructure @f _ (Prune @a) = withLowerOb @f @a (counit @(Lower f a))

instance P.Show (Struct (Supplies Comonoid) a b) where
  showsPrec _ Fork = P.showString "comult"
  showsPrec _ Prune = P.showString "counit"

instance
  ('[Supplies Monoid, Monoidal] `Elems` cs, Ob (a :: FREE cs (p :: CAT k)))
  => Monoid (a :: FREE cs p)
  where
  mempty = F.St Sprout F.Nil
  mappend = F.St Join F.Nil

-- | The free supply is commutative only up to interpretation ('FREE' has no equations); the marker
-- holds because every @'Proarrow.Category.Instance.Free.fold'@ of these arrows into a target lands in that target's commutative
-- monoid.
instance (Monoid (a :: FREE cs p), SymMonoidal (FREE cs p)) => CommutativeMonoid (a :: FREE cs p)

instance
  ('[Supplies Comonoid, Monoidal] `Elems` cs, Ob (a :: FREE cs (p :: CAT k)))
  => Comonoid (a :: FREE cs p)
  where
  counit = F.St Prune F.Nil
  comult = F.St Fork F.Nil

instance (Comonoid (a :: FREE cs p), SymMonoidal (FREE cs p)) => CocommutativeComonoid (a :: FREE cs p)

-- | Collapse an @n@-fold tensor power of a monoid with 'mappend', bottoming out at 'mempty'.
fanIn :: forall n a. (SNatI n, Monoid a) => NFold n a ~> a
fanIn = case snat @n of
  SZ -> mempty
  SS @n' -> mappend @a . (obj @a ** fanIn @n' @a)

-- | Dually, build an @n@-fold tensor power of a comonoid with 'comult', bottoming out at 'counit'.
fanOut :: forall n a. (SNatI n, Comonoid a) => a ~> NFold n a
fanOut = case snat @n of
  SZ -> counit
  SS @n' -> (obj @a ** fanOut @n' @a) . comult @a

-- | The 'Proarrow.Category.Monoidal.Strictified.Strictified' counterpart of 'fanIn'.
fanInS :: forall n a. (SNatI n, Monoid a) => NFoldS n a ~> '[a]
fanInS =
  case snat @n of
    SZ -> Str mempty
    SS @n' -> mappendS @a . (obj1 @a ** fanInS @n' @a)

-- | The 'Proarrow.Category.Monoidal.Strictified.Strictified' counterpart of 'fanOut'.
fanOutS :: forall n a. (SNatI n, Comonoid a) => '[a] ~> NFoldS n a
fanOutS =
  case snat @n of
    SZ -> Str counit
    SS @n' -> (obj1 @a ** fanOutS @n' @a) . comultS @a
