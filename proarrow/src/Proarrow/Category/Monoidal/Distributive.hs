{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Distributivity of a tensor over coproducts: a 'Distributive' category has 'distL'\/'distR' and
-- absorption by the initial object, and a 'DistributiveProfunctor' is monoidal for both tensor and
-- coproduct. Also home to 'Traversable' and 'Cotraversable' profunctors, which distribute any
-- 'StrongDistributiveProfunctor' and underlie 'Proarrow.Optic.Traversal.Traversal'.
module Proarrow.Category.Monoidal.Distributive where

import Data.Bifunctor (bimap)
import Data.Kind (Constraint, Type)
import Prelude qualified as P

import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..))
import Proarrow.Category.Instance.Free (Elems, FREE, Free (..), HasStructure (..), Lower, withLowerOb)
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , SymMonoidal (..)
  , Tensor
  , first
  , second
  , type (**!)
  )
import Proarrow.Category.Monoidal.Action (ActionAt, CoprodAction)
import Proarrow.Category.Monoidal.Closed (Closed (..), uncurry)
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard (..))
import Proarrow.Category.Monoidal.Strength (MonStrong, Strong (..))
import Proarrow.Colimit.BinaryCoproduct
  ( COPROD (..)
  , Coprod (..)
  , HasBinaryCoproducts (..)
  , HasCoproducts
  , codiag
  , (++)
  , type (+)
  )
import Proarrow.Colimit.Initial (HasInitialObject (..), InitF)
import Proarrow.Core (CAT, CategoryOf (..), Kind, Profunctor (..), Promonad (..), lmap, obj, (//), (:~>), type (+->))
import Proarrow.Monoid (Monoid (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), coindex, corepUniv)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Constant (Constant)
import Proarrow.Profunctor.Instance.Coproduct ((:+:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Instance.Product ((:*:) (..))
import Proarrow.Profunctor.Representable (CorepStar (..), Rep (..), RepCostar (..), Representable (..), repUniv)
import Proarrow.Tools.Laws (Inverses (..), Labelled (..), Laws (..), inverses)
import Prelude (($))

class (MonoidalProfunctor p, MonoidalProfunctor (Coprod p)) => DistributiveProfunctor p
instance (MonoidalProfunctor p, MonoidalProfunctor (Coprod p)) => DistributiveProfunctor p

-- | A distributive monoidal category: the tensor distributes over coproducts, and annihilates the
-- 'InitialObject'. The monoidal and coproduct worlds meet here.
--
-- __Laws:__
--
-- Each of the four arrows is invertible, with the named inverse:
--
-- * @'distL'@ is inverse to 'distLInv', and @'distR'@ to 'distRInv'
-- * @'absorbL'@ and @'absorbR'@ are inverse to 'Proarrow.Colimit.Initial.initiate'
--
-- Checked by 'Proarrow.Testing.Laws.testDistributive'.
class (Monoidal k, HasCoproducts k) => Distributive k where
  -- | Distributes a tensor on the left over a coproduct.
  distL :: (Ob (a :: k), Ob b, Ob c) => (a ** (b || c)) ~> (a ** b || a ** c)

  -- | Distributes a tensor on the right over a coproduct.
  distR :: (Ob (a :: k), Ob b, Ob c) => ((a || b) ** c) ~> (a ** c || b ** c)

  -- | The 'InitialObject' annihilates the tensor on the right.
  absorbL :: (Ob (a :: k)) => (a ** InitialObject) ~> InitialObject

  -- | The 'InitialObject' annihilates the tensor on the left.
  absorbR :: (Ob (a :: k)) => (InitialObject ** a) ~> InitialObject

-- | The structures the free category needs for 'Distributive', and those its laws are stated for.
type DistributiveStructures :: [Kind -> Constraint]
type DistributiveStructures = '[Monoidal, HasInitialObject, HasBinaryCoproducts, Distributive]

-- | The free-category structure for 'Distributive': formal distributors and absorbers,
-- interpreted by 'foldStructure' through the target's own. Together with the coproduct and
-- monoidal structures this makes a free category over a bare quiver distributive without asking
-- anything of the quiver's category.
instance
  (DistributiveStructures `Elems` cs)
  => HasStructure cs (p :: CAT k) Distributive
  where
  data Struct Distributive i o where
    DistL :: (Ob a, Ob b, Ob c) => Struct Distributive (a **! (b + c)) ((a **! b) + (a **! c))
    DistR :: (Ob a, Ob b, Ob c) => Struct Distributive ((a + b) **! c) ((a **! c) + (b **! c))
    AbsorbL :: (Ob a) => Struct Distributive (a **! InitF) InitF
    AbsorbR :: (Ob a) => Struct Distributive (InitF **! a) InitF
  foldStructure @f _ (DistL @a @b @c) =
    withLowerOb @f @a (withLowerOb @f @b (withLowerOb @f @c (distL @_ @(Lower f a) @(Lower f b) @(Lower f c))))
  foldStructure @f _ (DistR @a @b @c) =
    withLowerOb @f @a (withLowerOb @f @b (withLowerOb @f @c (distR @_ @(Lower f a) @(Lower f b) @(Lower f c))))
  foldStructure @f _ (AbsorbL @a) = withLowerOb @f @a (absorbL @_ @(Lower f a))
  foldStructure @f _ (AbsorbR @a) = withLowerOb @f @a (absorbR @_ @(Lower f a))

instance P.Show (Struct Distributive a b) where
  showsPrec _ DistL = P.showString "distL"
  showsPrec _ DistR = P.showString "distR"
  showsPrec _ AbsorbL = P.showString "absorbL"
  showsPrec _ AbsorbR = P.showString "absorbR"

instance (DistributiveStructures `Elems` cs) => Distributive (FREE cs (p :: CAT k)) where
  distL = St DistL Nil
  distR = St DistR Nil
  absorbL = St AbsorbL Nil
  absorbR = St AbsorbR Nil

distLInv
  :: forall {k} a b c. (Distributive k, Ob (a :: k), Ob b, Ob c) => (a ** b || a ** c) ~> (a ** (b || c))
distLInv = second @a (lft @k @b @c) ||| second @a (rgt @k @b @c)

distRInv
  :: forall {k} a b c. (Distributive k, Ob (a :: k), Ob b, Ob c) => (a ** c || b ** c) ~> ((a || b) ** c)
distRInv = first @c (lft @k @a @b) ||| first @c (rgt @k @a @b)

-- | Distributive promonads seem similar to selective applicative functors.
-- https://blog.veritates.love/selective_applicatives_theoretical_basis.html
branch
  :: forall {k} a b c i (p :: k +-> k)
   . (DistributiveProfunctor p, Promonad p, Distributive k, Ob a, Ob b, Ob c)
  => p i (a || b) -> p a c -> p b c -> p i c
branch pab pac pbc = rmap codiag ((pac ++ pbc) . pab)

instance Distributive Type where
  distL (a, e) = bimap (a,) (a,) e
  distR (e, c) = bimap (,c) (,c) e
  absorbL = P.snd
  absorbR = P.fst

instance Distributive () where
  distL = U.Unit
  distR = U.Unit
  absorbL = U.Unit
  absorbR = U.Unit

instance Distributive BOOL where
  distL @a @b @c = case obj @a of
    Fls -> Fls
    Tru -> obj @b +++ obj @c
  distR @a @b @c = case obj @c of
    Fls -> Fls
    Tru -> obj @a +++ obj @b
  absorbL = Fls
  absorbR = Fls

-- | A product of distributive categories distributes componentwise.
instance (Distributive j, Distributive k) => Distributive (j, k) where
  distL @'(a1, a2) @'(b1, b2) @'(c1, c2) = distL @j @a1 @b1 @c1 :**: distL @k @a2 @b2 @c2
  distR @'(a1, a2) @'(b1, b2) @'(c1, c2) = distR @j @a1 @b1 @c1 :**: distR @k @a2 @b2 @c2
  absorbL @'(a1, a2) = absorbL @j @a1 :**: absorbL @k @a2
  absorbR @'(a1, a2) = absorbR @j @a1 :**: absorbR @k @a2

distLClosed
  :: forall {k} (a :: k) (b :: k) (c :: k)
   . (Closed k, SymMonoidal k, HasBinaryCoproducts k, Ob a, Ob b, Ob c) => (a ** (b || c)) ~> (a ** b || a ** c)
distLClosed = (swap @k @b @a +++ swap @k @c @a) . distRClosed @b @c @a . withObCoprod @k @b @c (swap @k @a @(b || c))

distRClosed
  :: forall {k} (a :: k) (b :: k) (c :: k)
   . (Closed k, HasBinaryCoproducts k, Ob a, Ob b, Ob c) => ((a || b) ** c) ~> (a ** c || b ** c)
distRClosed =
  withOb2 @k @a @c $
    withOb2 @k @b @c $
      withObCoprod @k @(a ** c) @(b ** c) $
        uncurry @c (curry @k @a @c (lft @k @(a ** c) @(b ** c)) ||| curry @k @b @c (rgt @k @(a ** c) @(b ** c)))

class
  (DistributiveProfunctor (p :: k +-> k), MonStrong p, Strong CoprodAction p, Traversing p) =>
  StrongDistributiveProfunctor (p :: k +-> k)
instance
  (DistributiveProfunctor (p :: k +-> k), MonStrong p, Strong CoprodAction p, Traversing p)
  => StrongDistributiveProfunctor (p :: k +-> k)

-- | Distribution over a whole 'Traversable' witness, the @traverse'@ of the @profunctors@ library's
-- @Traversing@: a strong distributive profunctor built from 'one', '(**)', '(++)' and 'act' alone
-- only reaches finite shapes. The default runs the witness's own 'traverse', which for an unbounded
-- shape such as the list is a recursive value and needs a carrier whose values are functions, lazy
-- in 'dimap'. A carrier whose values are shapes, such as the generic optic carrier, absorbs the
-- witness instead. A 'Cotraversable' witness goes through @'CorepStar' t@ ('corepTraverse').
type Traversing :: forall {k}. (k +-> k) -> Constraint
class (Profunctor p) => Traversing (p :: k +-> k) where
  traverseP :: (Traversable t, Representable t) => t :.: p :~> p :.: t
  default traverseP :: (Traversable t, StrongDistributiveProfunctor p) => t :.: p :~> p :.: t
  traverseP = traverse

-- | With a representable traversable profunctor, you get a traversal a la one-liner.
repTraverse
  :: forall {k} (t :: k +-> k) p a b
   . (Traversable t, Representable t, Traversing p)
  => p a b -> p (t % a) (t % b)
repTraverse p = p // case traverseP (repUniv :.: p) of x :.: y -> rmap (index @t y) x

-- | With a corepresentable cotraversable profunctor, you get a co-traversal a la one-liner: a
-- corepresentable @t@ is @'RepCostar' ('CorepStar' t)@, so this is 'repTraverse' at @'CorepStar' t@.
corepTraverse
  :: forall {k} (t :: k +-> k) p a b
   . (Cotraversable t, Corepresentable t, Traversing p)
  => p a b -> p (t %% a) (t %% b)
corepTraverse = repTraverse @(CorepStar t)

-- | If both profunctors are representable, you get traversals as in base.
baseTraverse
  :: forall {k} (t :: k +-> k) f a b
   . (Traversable t, Representable t, Representable f, Traversing f, Ob b)
  => a ~> f % b -> t % a ~> f % (t % b)
baseTraverse = index . repTraverse @t @f @a @b . tabulate

instance (CopyDiscard k, HasCoproducts k, Monoid r) => Traversing (Rep (Constant r) :: k +-> k)
instance (SymMonoidal k, HasCoproducts k, Monoid m) => Traversing (Rep (ActionAt Tensor m) :: k +-> k)
instance (SymMonoidal k, HasCoproducts k) => Traversing (Id :: k +-> k)

-- | A composite carrier passes the witness through its halves in turn, so that each half can
-- absorb it.
instance (Traversing p, Traversing q) => Traversing (p :.: q) where
  traverseP (t :.: (p :.: q)) = case traverseP (t :.: p) of
    p' :.: t' -> case traverseP (t' :.: q) of
      q' :.: t'' -> (p' :.: q') :.: t''

-- | The constant functor absorbs a coproduct action: the injected summand is discarded onto
-- the monoid's unit, so this needs only copying\/discarding on the tensor side and coproducts.
instance (CopyDiscard k, HasCoproducts k, Monoid r) => Strong CoprodAction (Rep (Constant r) :: k +-> k) where
  act @(COPR a) (Rep @y p) = withObCoprod @k @a @y (Rep (mempty @r . discard @k @a ||| p))

-- | A witness that distributes any strong distributive profunctor through itself. For a
-- 'Representable' witness, callers go through 'traverseP' (or 'repTraverse'), which lets the carrier
-- absorb the witness instead of running 'traverse'.
type Traversable :: forall {k}. (k +-> k) -> Constraint
class (Profunctor t) => Traversable (t :: k +-> k) where
  traverse :: (StrongDistributiveProfunctor p) => t :.: p :~> p :.: t

instance (CategoryOf k) => Traversable (Id :: k +-> k) where
  traverse (Id f :.: p) = lmap f p :.: Id id \\ p

instance Traversable (->) where
  traverse (f :.: p) = lmap f p :.: id

instance (Traversable p, Traversable q) => Traversable (p :.: q) where
  traverse ((p :.: q) :.: r) = case traverse (q :.: r) of
    r' :.: q' -> case traverse (p :.: r') of
      r'' :.: p' -> r'' :.: (p' :.: q')

instance (Traversable p, Traversable q) => Traversable (p :+: q) where
  traverse (InjL p :.: r) = case traverse (p :.: r) of r' :.: p' -> r' :.: InjL p'
  traverse (InjR q :.: r) = case traverse (q :.: r) of r' :.: q' -> r' :.: InjR q'

-- | The dual of 'Traversable'. For a 'Corepresentable' witness, callers go through 'corepTraverse',
-- which is 'traverseP' at @'CorepStar' t@.
type Cotraversable :: forall {k}. (k +-> k) -> Constraint
class (Profunctor t) => Cotraversable (t :: k +-> k) where
  cotraverse :: (StrongDistributiveProfunctor (p :: k +-> k)) => p :.: t :~> t :.: p

instance (CategoryOf k) => Cotraversable (Id :: k +-> k) where
  cotraverse (p :.: Id f) = Id id :.: rmap f p \\ p

instance Cotraversable (->) where
  cotraverse (p :.: f) = id :.: rmap f p

instance (Cotraversable p, Cotraversable q) => Cotraversable (p :.: q) where
  cotraverse (r :.: (p :.: q)) = case cotraverse (r :.: p) of
    p' :.: r' -> case cotraverse (r' :.: q) of
      q' :.: r'' -> (p' :.: q') :.: r''

instance (HasBinaryCoproducts k, Cotraversable p, Cotraversable q) => Cotraversable ((p :: k +-> k) :*: q) where
  cotraverse (r :.: (p :*: q)) = case (cotraverse (r :.: p), cotraverse (r :.: q)) of
    ((:.:) @a p' r', (:.:) @b q' r'') -> (rmap (lft @k @a @b) p' :*: rmap (rgt @k @a @b) q') :.: rmap codiag (r' ++ r'') \\ p \\ p' \\ q'

instance (Cotraversable p, Cotraversable q) => Cotraversable (p :+: q) where
  cotraverse (r :.: InjL p) = case cotraverse (r :.: p) of p' :.: r' -> InjL p' :.: r'
  cotraverse (r :.: InjR q) = case cotraverse (r :.: q) of q' :.: r' -> InjR q' :.: r'

-- | A corepresentable cotraversable witness, read as a traversable one.
instance (Cotraversable t, Corepresentable t) => Traversable (CorepStar t) where
  traverse (CorepStar l :.: p) =
    p // case cotraverse @t (p :.: corepUniv) of
      t' :.: p' -> lmap (coindex t' . l) p' :.: repUniv

instance (Traversable t, Representable t) => Cotraversable (RepCostar t) where
  cotraverse (p :.: RepCostar t) = p // case traverseP @_ @t (repUniv :.: p) of p' :.: t' -> corepUniv :.: rmap (t . index t') p'

-- | The tensor distributes over coproducts and is absorbed by the initial object:
-- 'distL', 'distR', 'absorbL' and 'absorbR' are isomorphisms, with the inverses 'distLInv',
-- 'distRInv' and 'initiate'.
instance Laws DistributiveStructures where
  laws =
    inverses "distL" (\ @a @b @c -> Inverses (distL @_ @a @b @c) (label "distLInv" (distLInv @a @b @c)))
      P.++ inverses "distR" (\ @a @b @c -> Inverses (distR @_ @a @b @c) (label "distRInv" (distRInv @a @b @c)))
      P.++ inverses
        "absorbL"
        (\ @a -> withOb2 @_ @a @InitialObject (Inverses (absorbL @_ @a) initiate))
      P.++ inverses
        "absorbR"
        (\ @a -> withOb2 @_ @InitialObject @a (Inverses (absorbR @_ @a) initiate))
