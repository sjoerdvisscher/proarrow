{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Monoids and comonoids internal to a monoidal category: a 'Monoid' @m@ has @'mempty' :: 'Unit' '~>' m@
-- and @'mappend' :: m '**' m '~>' m@; dually a 'Comonoid' has 'counit' and 'comult'. Monoids in
-- 'Data.Kind.Type' are exactly Prelude monoids, and in a cartesian category every object is a comonoid.
module Proarrow.Monoid where

import Data.Kind (Constraint, Type)
import Prelude qualified as P

import Proarrow.Category.Instance.Free (Elem, FREE, HasStructure (..), IsFreeOb (..))
import Proarrow.Category.Instance.Free qualified as F
import Proarrow.Category.Instance.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , SymMonoidal (..)
  , Tensor
  , UnitF
  , swapInner
  , (**)
  , type (**!)
  )
import Proarrow.Category.Monoidal.Action (Act, ActionAt, CoprodAction, MonoidalAction (..), actHom)
import Proarrow.Category.Monoidal.Closed (Closed (..), Exp)
import Proarrow.Category.Monoidal.CompactClosed (CompactClosed (..))
import Proarrow.Category.Monoidal.StarAutonomous (StarAutonomous (..))
import Proarrow.Category.Monoidal.Strength (Strong (..))
import Proarrow.Category.Monoidal.Strictified (Strictified (..))
import Proarrow.Colimit.BinaryCoproduct
  ( COPROD (..)
  , Coprod (..)
  , HasBinaryCoproducts (..)
  , HasBiproducts (..)
  , HasCoproducts
  , codiag
  )
import Proarrow.Colimit.Initial (HasInitialObject (..), HasZeroObject (..))
import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Kind
  , Profunctor (..)
  , Promonad (..)
  , arr
  , dimapDefault
  , obj
  , (//)
  , type (+->)
  )
import Proarrow.Limit.BinaryProduct (Cartesian, HasBinaryProducts (..), HasProducts, PROD (..), Prod (..), diag, (&&&))
import Proarrow.Limit.Terminal (HasTerminalObject (..))
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

newtype GenElt x m = GenElt (x ~> m)

instance (Monoid m, Cartesian k) => P.Semigroup (GenElt x (m :: k)) where
  GenElt f <> GenElt g = GenElt (mappend . (f &&& g))
instance (Monoid m, Cartesian k, Ob x) => P.Monoid (GenElt x (m :: k)) where
  mempty = GenElt (mempty . arr terminate)

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

instance Comonoid (a :: Type) where
  counit _ = ()
  comult a = (a, a)
instance CocommutativeComonoid (a :: Type)

instance Comonoid '() where
  counit = id
  comult = id
instance CocommutativeComonoid '()

instance (HasProducts k, Ob a) => Comonoid (PR (a :: k)) where
  counit = Prod terminate
  comult = Prod diag
instance (HasProducts k, Ob a) => CocommutativeComonoid (PR (a :: k))

counitAct :: forall {m} {c} t (a :: m) (n :: c). (MonoidalAction t, Comonoid a, Ob n) => Act t a n ~> n
counitAct = unitor @t . actHom @t (counit @a) (obj @n)

comultAct
  :: forall {m} {c} t (a :: m) (n :: c). (MonoidalAction t, Comonoid a, Ob n) => Act t a n ~> Act t a (Act t a n)
comultAct = multiplicator @t @a @a @n . actHom @t (comult @a) (obj @n)

-- | @'Supplies' c k@ says that every object of the category @k@ satisfies the constraint @c@ --
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

type data MONOIDK (m :: k) = M
data Mon a b where
  Mon :: Unit ~> m -> Mon (M :: MONOIDK m) M
instance (Monoid m) => Profunctor (Mon :: CAT (MONOIDK m)) where
  dimap = dimapDefault
  r \\ Mon{} = r
instance (Monoid m) => Promonad (Mon :: CAT (MONOIDK m)) where
  id = Mon mempty
  Mon f . Mon g = Mon (combine f g)

-- | A monoid as a one object category.
instance (Monoid m) => CategoryOf (MONOIDK m) where
  type (~>) = Mon
  type Ob a = a P.~ M

instance (Monoid m) => HasInitialObject (MONOIDK m) where
  type InitialObject = M
  initiate = Mon mempty
instance (Monoid m) => HasTerminalObject (MONOIDK m) where
  type TerminalObject = M
  terminate = Mon mempty
instance (Monoid m) => HasBinaryProducts (MONOIDK m) where
  type a && b = M
  withObProd @M @M r = r
  fst @M @M = Mon mempty
  snd @M @M = Mon mempty
  Mon f &&& Mon g = Mon (combine f g)
instance (Monoid m) => HasBinaryCoproducts (MONOIDK m) where
  type a || b = M
  withObCoprod @M @M r = r
  lft @M @M = Mon mempty
  rgt @M @M = Mon mempty
  Mon f ||| Mon g = Mon (combine f g)

instance (CommutativeMonoid m) => MonoidalProfunctor (Mon :: CAT (MONOIDK m)) where
  one = Mon mempty
  Mon f ** Mon g = Mon (combine f g)
instance (CommutativeMonoid m) => Monoidal (MONOIDK m) where
  type Unit = M
  type M ** M = M
  withOb2 r = r
  leftUnitor = Mon mempty
  leftUnitorInv = Mon mempty
  rightUnitor = Mon mempty
  rightUnitorInv = Mon mempty
  associator = Mon mempty
  associatorInv = Mon mempty
instance (CommutativeMonoid m) => SymMonoidal (MONOIDK m) where
  swap = Mon mempty

instance (CommutativeMonoid m) => StarAutonomous (MONOIDK m) where
  type Dual (M :: MONOIDK m) = M
  withObDual r = r
  dual f@Mon{} = f
  dualInv f = f
  linDist _ = id
  linDistInv _ = id
instance (CommutativeMonoid m) => CompactClosed (MONOIDK m) where
  distribDual = Mon mempty
  dualUnit = Mon mempty
instance (CommutativeMonoid m) => Closed (MONOIDK m) where
  type a ~~> b = M
  withObExp r = r
  curry (Mon m) = Mon m
  apply = Mon mempty

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

instance (Cartesian k, Ob r) => Strong Tensor (Rep (Constant r) :: k +-> k) where
  act @a (Rep @y p) = withOb2 @k @a @y (Rep (p . snd @k @a)) \\ p

instance (Cartesian k, HasCoproducts k, Monoid r) => Strong CoprodAction (Rep (Constant r) :: k +-> k) where
  act @(COPR a) (Rep @y p) = withObCoprod @k @a @y (Rep (mempty @r . terminate @k @a ||| p))

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
-- 'Proarrow.Category.Monoidal.Distributive.StrongDistributiveProfunctor', which is what makes a
-- 'Proarrow.Optic.Grate.Grate' a 'Proarrow.Optic.Kaleidoscope.Kaleidoscope'.
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
instance (Supplies Monoid `Elem` cs, Monoidal `Elem` cs) => HasStructure cs p (Supplies Monoid) where
  data Struct (Supplies Monoid) i o where
    Join :: (Ob a) => Struct (Supplies Monoid) (a **! a) a
    Sprout :: (Ob a) => Struct (Supplies Monoid) UnitF a
  foldStructure @f _ (Join @a) = withLowerOb @a @f (mappend @(Lower f a))
  foldStructure @f _ (Sprout @a) = withLowerOb @a @f (mempty @(Lower f a))

instance P.Show (Struct (Supplies Monoid) a b) where
  showsPrec _ Join = P.showString "mappend"
  showsPrec _ Sprout = P.showString "mempty"

-- | The free-category structure for @'Supplies' 'Comonoid'@, dually: formal 'comult' ('Fork') and
-- 'counit' ('Prune') generators for every object.
instance (Supplies Comonoid `Elem` cs, Monoidal `Elem` cs) => HasStructure cs p (Supplies Comonoid) where
  data Struct (Supplies Comonoid) i o where
    Fork :: (Ob a) => Struct (Supplies Comonoid) a (a **! a)
    Prune :: (Ob a) => Struct (Supplies Comonoid) a UnitF
  foldStructure @f _ (Fork @a) = withLowerOb @a @f (comult @(Lower f a))
  foldStructure @f _ (Prune @a) = withLowerOb @a @f (counit @(Lower f a))

instance P.Show (Struct (Supplies Comonoid) a b) where
  showsPrec _ Fork = P.showString "comult"
  showsPrec _ Prune = P.showString "counit"

instance
  (Supplies Monoid `Elem` cs, Monoidal `Elem` cs, Monoidal (FREE cs p), Ob (a :: FREE cs p))
  => Monoid (a :: FREE cs p)
  where
  mempty = F.St Sprout F.Id
  mappend = F.St Join F.Id

-- | The free supply is commutative only up to interpretation ('FREE' has no equations); the marker
-- holds because every @'Proarrow.Category.Instance.Free.fold'@ of these arrows into a target lands in that target's commutative
-- monoid.
instance (Monoid (a :: FREE cs p), SymMonoidal (FREE cs p)) => CommutativeMonoid (a :: FREE cs p)

instance
  (Supplies Comonoid `Elem` cs, Monoidal `Elem` cs, Monoidal (FREE cs p), Ob (a :: FREE cs p))
  => Comonoid (a :: FREE cs p)
  where
  counit = F.St Prune F.Id
  comult = F.St Fork F.Id

instance (Comonoid (a :: FREE cs p), SymMonoidal (FREE cs p)) => CocommutativeComonoid (a :: FREE cs p)
