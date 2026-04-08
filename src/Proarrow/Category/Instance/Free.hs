{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Instance.Free where

import Data.Char (toLower)
import Data.Kind (Constraint)
import Data.Typeable (Typeable, eqT, (:~:) (..))
import Prelude (Bool (..), Eq (..), Maybe (..), Show (..), (&&))
import Prelude qualified as P

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Kind
  , Profunctor (..)
  , Promonad (..)
  , UN
  , dimapDefault
  , type (+->)
  )
import Proarrow.Profunctor.Initial (InitialProfunctor)
import Proarrow.Profunctor.Representable (Representable (..), withRepOb)

type family All (cs :: [Kind -> Constraint]) (k :: Kind) :: Constraint where
  All '[] k = ()
  All (c ': cs) k = (c k, All cs k)

class ((All cs k) => c k) => FromAll cs c k
instance ((All cs k) => c k) => FromAll cs c k

type Elem :: (Kind -> Constraint) -> [Kind -> Constraint] -> Constraint
class (forall k. FromAll cs c k) => c `Elem` cs
instance {-# OVERLAPPABLE #-} (c `Elem` cs) => c `Elem` (d ': cs)
instance c `Elem` (c ': cs)

newtype FREE (cs :: [Kind -> Constraint]) (p :: CAT j) = EMB j
type instance UN EMB (EMB a) = a

type Free :: CAT (FREE cs p)
data Free a b where
  Id :: (Ob a) => Free a a
  Emb :: (Ob a, Ob b, Typeable a, Typeable b) => p a b %1 -> Free (i :: FREE cs p) (EMB a) %1 -> Free i (EMB b)
  Str
    :: forall {j} {cs} {p :: CAT j} (c :: Kind -> Constraint) (a :: FREE cs p) b i
     . (HasStructure cs p c, Ob a, Ob b)
    => Struct c a b %1 -> Free i a %1 -> Free i b

emb :: (Ob a, Ob b, Typeable a, Typeable b, Ok cs p) => p a b %1 -> Free (EMB a :: FREE cs p) (EMB b)
emb p = Emb p Id

class (forall x y. Eq (p x y)) => Eq2 p
instance (forall x y. Eq (p x y)) => Eq2 p

class (forall x y. P.Show (p x y)) => Show2 p
instance (forall x y. P.Show (p x y)) => Show2 p

class (Typeable p, Typeable cs, Typeable j, All cs (FREE cs p)) => Ok cs (p :: CAT j)
instance (Typeable p, Typeable cs, Typeable j, All cs (FREE cs p)) => Ok cs (p :: CAT j)

class (Ok c p, Eq2 p) => WithEq (a :: FREE c (p :: CAT j))
instance (Ok c p, Eq2 p) => WithEq (a :: FREE c (p :: CAT j))

instance (WithEq a) => Eq (Free a b) where
  Id == Id = True
  Emb @al p1 g1 == Emb @ar p2 g2 = case eqT @al @ar of Just Refl -> p1 == p2 && g1 == g2; Nothing -> False
  Str @strl @a1 s1 g1 == Str @strr @a2 s2 g2 = case (eqT @strl @strr, eqT @a1 @a2) of
    (Just Refl, Just Refl) -> s1 == s2 && g1 == g2
    _ -> False
  _ == _ = False

class (Show2 p) => WithShow (a :: FREE c (p :: CAT j))
instance (Show2 p) => WithShow (a :: FREE c (p :: CAT j))

instance (WithShow a) => Show (Free a b) where
  showsPrec _ Id = P.showString "id"
  showsPrec d (Emb p g) = P.map toLower . showPostComp d p g
  showsPrec d (Str s g) = P.map toLower . showPostComp d s g

showPostComp :: (Show p, WithShow a) => P.Int -> p -> Free a b -> P.ShowS
showPostComp d p Id = P.showsPrec d p
showPostComp d p g = P.showParen (d P.> 9) (P.showsPrec 10 p . P.showString " . " . P.showsPrec 10 g)

type IsFreeOb :: forall {j} {cs :: [Kind -> Constraint]} {p :: CAT j}. FREE cs p -> Constraint
class IsFreeOb (a :: FREE cs (p :: CAT j)) where
  type Lower (f :: j +-> k) (a :: FREE cs p) :: k
  withLowerOb :: forall {k} (f :: j +-> k) r. (Representable f, All cs k) => ((Ob (Lower f (a :: FREE cs p))) => r) -> r
instance (Ob a, Typeable a) => IsFreeOb (EMB a) where
  type Lower f (EMB a) = f % a
  withLowerOb @f = withRepOb @f @a

class ((Ok cs p, Eq2 p) => Eq2 str, (Ok cs p) => Typeable str, (Show2 p) => Show2 str) => CanEqShow (str :: CAT (FREE cs p))
instance ((Ok cs p, Eq2 p) => Eq2 str, (Ok cs p) => Typeable str, (Show2 p) => Show2 str) => CanEqShow (str :: CAT (FREE cs p))

class
  (Typeable c, CanEqShow (Struct c :: CAT (FREE cs p)), c `Elem` cs) =>
  HasStructure cs (p :: CAT j) (c :: Kind -> Constraint)
  where
  data Struct c :: CAT (FREE cs p)
  foldStructure
    :: forall {k} (f :: j +-> k) (a :: FREE cs p) (b :: FREE cs p)
     . (All cs k, Representable f)
    => (forall (x :: FREE cs p) y. x ~> y -> Lower f x ~> Lower f y)
    -> Struct c a b
    -> Lower f a ~> Lower f b

fold
  :: forall {j} {k} {p :: CAT j} (cs :: [Kind -> Constraint]) (f :: j +-> k) (a :: FREE cs p) (b :: FREE cs p)
   . (All cs k, Representable f)
  => (forall x y. p x y -> (f % x) ~> (f % y))
  -> a ~> b
  -> Lower f a ~> Lower f b
fold pn = go
  where
    go :: forall (x :: FREE cs p) y. x ~> y -> Lower f x ~> Lower f y
    go Id = withLowerOb @x @f id
    go (Emb p g) = pn p . go g
    go (Str s g) = foldStructure @_ @_ @_ @_ @f go s . go g

retract
  :: forall {j} {k} cs (f :: j +-> k) a b
   . (All cs k, Representable f) => (a :: FREE cs InitialProfunctor) ~> b -> Lower f a ~> Lower f b
retract = fold @cs @f (\case {})

instance (Ok cs p) => CategoryOf (FREE cs p) where
  type (~>) = Free
  type Ob a = (IsFreeOb a, Typeable a)

instance (Ok cs p) => Promonad (Free :: CAT (FREE cs p)) where
  id = Id
  Id . g = g
  f . Id = f
  Emb p f . g = Emb p (f . g)
  Str s f . g = Str s (f . g)

instance (Ok cs p) => Profunctor (Free :: CAT (FREE cs p)) where
  dimap = dimapDefault
  r \\ Id = r
  r \\ Emb _ f = r \\ f
  r \\ Str _ f = r \\ f

data family UnitF :: k
instance (Monoidal `Elem` cs) => IsFreeOb (UnitF :: FREE cs p) where
  type Lower f UnitF = Unit
  withLowerOb r = r
data family (**!) (a :: k) (b :: k) :: k
instance (Ob (a :: FREE cs p), Ob b, Monoidal `Elem` cs) => IsFreeOb (a **! b) where
  type Lower f (a **! b) = Lower f a ** Lower f b
  withLowerOb @f r = withLowerOb @a @f (withLowerOb @b @f (withOb2 @_ @(Lower f a) @(Lower f b) r))
instance (Monoidal `Elem` cs) => HasStructure cs p Monoidal where
  data Struct Monoidal i o where
    Par0 :: Struct Monoidal UnitF UnitF
    Par :: a ~> b -> c ~> d -> Struct Monoidal (a **! c) (b **! d)
    LeftUnitor :: (Ob a) => Struct Monoidal (UnitF **! a) a
    LeftUnitorInv :: (Ob a) => Struct Monoidal a (UnitF **! a)
    RightUnitor :: (Ob a) => Struct Monoidal (a **! UnitF) a
    RightUnitorInv :: (Ob a) => Struct Monoidal a (a **! UnitF)
    Associator :: (Ob a, Ob b, Ob c) => Struct Monoidal ((a **! b) **! c) (a **! (b **! c))
    AssociatorInv :: (Ob a, Ob b, Ob c) => Struct Monoidal (a **! (b **! c)) ((a **! b) **! c)
  foldStructure _ Par0 = par0
  foldStructure go (Par f g) = go f `par` go g
  foldStructure @f _ (LeftUnitor @a) = withLowerOb @a @f leftUnitor
  foldStructure @f _ (LeftUnitorInv @a) = withLowerOb @a @f leftUnitorInv
  foldStructure @f _ (RightUnitor @a) = withLowerOb @a @f rightUnitor
  foldStructure @f _ (RightUnitorInv @a) = withLowerOb @a @f rightUnitorInv
  foldStructure @f _ (Associator @a @b @c') = withLowerOb @a @f (withLowerOb @b @f (withLowerOb @c' @f (associator @_ @(Lower f a) @(Lower f b) @(Lower f c'))))
  foldStructure @f _ (AssociatorInv @a @b @c') = withLowerOb @a @f (withLowerOb @b @f (withLowerOb @c' @f (associatorInv @_ @(Lower f a) @(Lower f b) @(Lower f c'))))
deriving instance (WithEq a) => Eq (Struct Monoidal a b)
deriving instance (WithShow a) => Show (Struct Monoidal a b)
instance (Ok cs p, Monoidal `Elem` cs) => MonoidalProfunctor (Free :: CAT (FREE cs p)) where
  par0 = Str Par0 Id
  f `par` g = Str (Par f g) Id \\ f \\ g
instance (Ok cs p, Monoidal `Elem` cs) => Monoidal (FREE cs p) where
  type Unit = UnitF
  type a ** b = a **! b
  withOb2 r = r
  leftUnitor = Str LeftUnitor Id
  leftUnitorInv = Str LeftUnitorInv Id
  rightUnitor = Str RightUnitor Id
  rightUnitorInv = Str RightUnitorInv Id
  associator = Str Associator Id
  associatorInv = Str AssociatorInv Id

instance (SymMonoidal `Elem` cs) => HasStructure cs p SymMonoidal where
  data Struct SymMonoidal i o where
    Swap :: (Ob a, Ob b) => Struct SymMonoidal (a **! b) (b **! a)
  foldStructure @f _ (Swap @a @b) = withLowerOb @a @f (withLowerOb @b @f (swap @_ @(Lower f a) @(Lower f b)))
deriving instance (WithEq a) => Eq (Struct SymMonoidal a b)
deriving instance (WithShow a) => Show (Struct SymMonoidal a b)
instance (Ok cs p, SymMonoidal `Elem` cs, Monoidal `Elem` cs) => SymMonoidal (FREE cs p) where
  swap = Str Swap Id