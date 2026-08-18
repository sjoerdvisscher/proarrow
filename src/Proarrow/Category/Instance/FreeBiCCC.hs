{-# LANGUAGE AllowAmbiguousTypes #-}

-- | The free bicartesian closed category on a generating profunctor @p@.
--
-- Unlike "Proarrow.Category.Instance.Free" (which is generic over an arbitrary /list/ of
-- structures), this is hardcoded to exactly the BiCCC signature, to simplify the implementation.
module Proarrow.Category.Instance.FreeBiCCC
  ( FBC (..)
  , Term (..)
  , Lower
  , interp
  , KnownFBCOb (fbcCase)
  , fbcOb
  ) where

import Data.Kind (Constraint)
import Prelude (type (~))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Closed (BiCCC, Closed (..))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, type (+->))
import Proarrow.Limit.BinaryProduct
  ( HasBinaryProducts (..)
  , associatorProd
  , associatorProdInv
  , leftUnitorProd
  , leftUnitorProdInv
  , rightUnitorProd
  , rightUnitorProdInv
  , swapProd
  )
import Proarrow.Limit.Terminal (HasTerminalObject (..))

-- | Object expressions of the free BiCCC on generators @p@: base objects (@OBJ@, carrying an
-- actual object of @k@ — the category @p@'s generating morphisms are themselves between),
-- plus terminal\/initial objects and products, coproducts and exponentials of
-- sub-expressions.
type data FBC (p :: k +-> k)
  = OBJ k
  | UNIT
  | PROD (FBC p) (FBC p)
  | ZERO
  | SUM (FBC p) (FBC p)
  | EXPO (FBC p) (FBC p)

-- | Interpret an object expression as the object of @k@ it denotes.
type family Lower (a :: FBC p) :: k where
  Lower (OBJ x) = x
  Lower UNIT = TerminalObject
  Lower (PROD a b) = Lower a && Lower b
  Lower ZERO = InitialObject
  Lower (SUM a b) = Lower a || Lower b
  Lower (EXPO a b) = Lower a ~~> Lower b

-- | A term of the free BiCCC: one constructor per operation, including composition itself.
-- No smart constructors, no normal forms — e.g. @Compose Id f@ and @f@ are different 'Term's
-- that happen to interpret to the same morphism. @p@ (and the base category @k@ it's a
-- profunctor on) is carried purely by the kind of @a@/@b@ (@FBC p@), the same way
-- "Proarrow.Category.Instance.Free"'s @Free@ carries its generating profunctor, so it doesn't
-- need to be an explicit parameter of 'Term' itself.
type Term :: CAT (FBC p)
data Term a b where
  Id :: (Ob a) => Term a a
  Compose :: Term b c -> Term a b -> Term a c
  Emb :: (Ob x, Ob y) => p x y -> Term (OBJ x :: FBC p) (OBJ y)
  Terminate :: (Ob a) => Term a UNIT
  Absurd :: (Ob a) => Term ZERO a
  Fst :: (Ob a, Ob b) => Term (PROD a b) a
  Snd :: (Ob a, Ob b) => Term (PROD a b) b
  Pair :: Term c a -> Term c b -> Term c (PROD a b)
  Inl :: (Ob a, Ob b) => Term a (SUM a b)
  Inr :: (Ob a, Ob b) => Term b (SUM a b)
  Case :: Term a c -> Term b c -> Term (SUM a b) c
  Curry :: (Ob a, Ob b) => Term (PROD a b) c -> Term a (EXPO b c)
  Apply :: (Ob a, Ob b) => Term (PROD (EXPO a b) a) b

instance forall k (p :: k +-> k). (BiCCC k) => Profunctor (Term :: CAT (FBC p)) where
  dimap = dimapDefault
  r \\ Id = r
  r \\ Compose g f = r \\ g \\ f
  r \\ Emb _ = r
  r \\ Terminate = r
  r \\ Absurd = r
  r \\ (Fst @a @b) = withObProd @_ @(Lower a) @(Lower b) r
  r \\ (Snd @a @b) = withObProd @_ @(Lower a) @(Lower b) r
  r \\ (Pair @_ @a @b f g) = withObProd @_ @(Lower a) @(Lower b) r \\ f \\ g
  r \\ (Inl @a @b) = withObCoprod @_ @(Lower a) @(Lower b) r
  r \\ (Inr @a @b) = withObCoprod @_ @(Lower a) @(Lower b) r
  r \\ (Case @a @_ @b f g) = withObCoprod @_ @(Lower a) @(Lower b) r \\ f \\ g
  r \\ (Curry @_ @b @c f) = withObExp @_ @(Lower b) @(Lower c) r \\ f
  r \\ (Apply @a @b) = withObExp @_ @(Lower a) @(Lower b) (withObProd @_ @(Lower a ~~> Lower b) @(Lower a) r)

instance forall k (p :: k +-> k). (BiCCC k) => Promonad (Term :: CAT (FBC p)) where
  id = Id
  (.) = Compose
instance forall k (p :: k +-> k). (BiCCC k) => CategoryOf (FBC p) where
  type (~>) = Term
  type Ob (a :: FBC (p :: k +-> k)) = (Ob (Lower a :: k), KnownFBCOb a)

-- | Witnesses that an object expression is well-formed by case analysis on its shape.
type KnownFBCOb :: forall {k} {p :: k +-> k}. FBC p -> Constraint
class KnownFBCOb (a :: FBC (p :: k +-> k)) where
  fbcCase
    :: (forall x. (a ~ OBJ x, Ob (x :: k)) => r)
    -> ((a ~ UNIT) => r)
    -> (forall x y. (a ~ PROD x y, Ob x, Ob y) => r)
    -> ((a ~ ZERO) => r)
    -> (forall x y. (a ~ SUM x y, Ob x, Ob y) => r)
    -> (forall x y. (a ~ EXPO x y, Ob x, Ob y) => r)
    -> r

instance (Ob x) => KnownFBCOb (OBJ x :: FBC p) where
  fbcCase o _ _ _ _ _ = o

instance forall k (p :: k +-> k). (BiCCC k) => KnownFBCOb (UNIT :: FBC p) where
  fbcCase _ u _ _ _ _ = u

instance forall k (p :: k +-> k). (BiCCC k) => KnownFBCOb (ZERO :: FBC p) where
  fbcCase _ _ _ z _ _ = z

instance forall k (p :: k +-> k) a b. (BiCCC k, KnownFBCOb (a :: FBC p), KnownFBCOb b) => KnownFBCOb (PROD a b) where
  fbcCase _ _ prod _ _ _ = withLowerOb @a (withLowerOb @b prod)

instance forall k (p :: k +-> k) a b. (BiCCC k, KnownFBCOb (a :: FBC p), KnownFBCOb b) => KnownFBCOb (SUM a b) where
  fbcCase _ _ _ _ sm _ = withLowerOb @a (withLowerOb @b sm)

instance forall k (p :: k +-> k) a b. (BiCCC k, KnownFBCOb (a :: FBC p), KnownFBCOb b) => KnownFBCOb (EXPO a b) where
  fbcCase _ _ _ _ _ ex = withLowerOb @a (withLowerOb @b ex)

-- | Recover 'Ob' of the /interpreted/ shape (needed to call @k@'s own 'withObProd'\/
-- 'withObCoprod'\/'withObExp') from only the /leaves'/ 'Ob', by case analysis via 'fbcCase' —
-- deliberately weaker than requiring the already-bundled, full 'Ob' of the sub-shapes, since
-- that would make it impossible to ever construct in the first place (needing 'Ob' of a
-- compound shape to construct 'Ob' of a bigger compound shape containing it).
withLowerOb :: forall {k} {p :: k +-> k} a r. (BiCCC k, KnownFBCOb (a :: FBC p)) => ((Ob (Lower a :: k)) => r) -> r
withLowerOb r =
  fbcCase @a
    r
    r
    (\ @x @y -> withObProd @k @(Lower x) @(Lower y) r)
    r
    (\ @x @y -> withObCoprod @k @(Lower x) @(Lower y) r)
    (\ @x @y -> withObExp @k @(Lower x) @(Lower y) r)

-- | The identity morphism on @a@, recovered by case analysis via 'fbcCase' — the only place
-- 'KnownFBCOb' is needed once it's bundled into 'Ob' (see 'CategoryOf' above): everywhere else,
-- an 'Ob' proof in hand is already enough, and 'Proarrow.Object.obj' gives the identity directly.
fbcOb :: forall {k} {p :: k +-> k} a. (BiCCC k, KnownFBCOb (a :: FBC p)) => Term a a
fbcOb =
  fbcCase @a
    Id
    Id
    (\ @x @y -> withObProd @(FBC p) @x @y Id)
    Id
    (\ @x @y -> withObCoprod @(FBC p) @x @y Id)
    (\ @x @y -> withObExp @(FBC p) @x @y Id)

instance forall k (p :: k +-> k). (BiCCC k) => HasTerminalObject (FBC p) where
  type TerminalObject = UNIT
  terminate = Terminate
instance forall k (p :: k +-> k). (BiCCC k) => HasInitialObject (FBC p) where
  type InitialObject = ZERO
  initiate = Absurd

instance forall k (p :: k +-> k). (BiCCC k) => HasBinaryProducts (FBC p) where
  type a && b = PROD a b
  withObProd @a @b r = withObProd @k @(Lower a) @(Lower b) r
  fst = Fst
  snd = Snd
  f &&& g = Pair f g \\ f

instance forall k (p :: k +-> k). (BiCCC k) => HasBinaryCoproducts (FBC p) where
  type a || b = SUM a b
  withObCoprod @a @b r = withObCoprod @k @(Lower a) @(Lower b) r
  lft = Inl
  rgt = Inr
  f ||| g = Case f g \\ f

instance forall k (p :: k +-> k). (BiCCC k) => MonoidalProfunctor (Term :: CAT (FBC p)) where
  one = id
  (**) = (***)
instance forall k (p :: k +-> k). (BiCCC k) => Monoidal (FBC p) where
  type a ** b = a && b
  type Unit = TerminalObject
  withOb2 @a @b = withObProd @_ @a @b
  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator @a @b @c = associatorProd @a @b @c
  associatorInv @a @b @c = associatorProdInv @a @b @c
instance forall k (p :: k +-> k). (BiCCC k) => SymMonoidal (FBC p) where
  swap @a @b = swapProd @a @b

instance forall k (p :: k +-> k). (BiCCC k) => Closed (FBC p) where
  type a ~~> b = EXPO a b
  withObExp @a @b r = withObExp @k @(Lower a) @(Lower b) r
  curry = Curry
  apply = Apply

-- | Interpret a 'Term' as the morphism of @k@ it denotes, given an interpretation of the
-- generators, provided @k@ is itself a BiCCC. This is the one place a 'Term''s meaning is
-- pinned down; everything else (including equality) is defined in terms of it.
interp
  :: forall {k} (p :: k +-> k) src tgt
   . (BiCCC k)
  => (forall x y. p x y -> x ~> y)
  -> Term (src :: FBC p) tgt
  -> Lower src ~> Lower tgt
interp _ Id = id
interp gn (Compose g f) = interp gn g . interp gn f
interp gn (Emb g) = gn g
interp _ Terminate = terminate
interp _ Absurd = initiate
interp _ (Fst @a @b) = fst @_ @(Lower a) @(Lower b)
interp _ (Snd @a @b) = snd @_ @(Lower a) @(Lower b)
interp gn (Pair f g) = interp gn f &&& interp gn g
interp _ (Inl @a @b) = lft @_ @(Lower a) @(Lower b)
interp _ (Inr @a @b) = rgt @_ @(Lower a) @(Lower b)
interp gn (Case f g) = interp gn f ||| interp gn g
interp gn (Curry @a @b @c f) = curry @_ @(Lower a) @(Lower b) @(Lower c) (interp gn f)
interp _ (Apply @a @b) = apply @_ @(Lower a) @(Lower b)
