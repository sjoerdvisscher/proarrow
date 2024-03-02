{-# LANGUAGE AllowAmbiguousTypes, IncoherentInstances #-}
module Proarrow.Category.Monoidal.Optic where

import Data.Kind (Type)
import Data.Functor.Identity (Identity (..))
import Data.Functor.Compose (Compose (..))
import Prelude (uncurry, Either, either, fst, snd, ($), Maybe (..), const, Traversable, Monad (..), fmap)

import Proarrow.Core (CategoryOf (..), PRO, Profunctor (..), Promonad (..), UN, OB, Kind, CAT, dimapDefault)
import Proarrow.Category.Monoidal (Monoidal(..))
import Proarrow.Category.Monoidal.Product ()
import Proarrow.Category.Instance.Nat (Nat (..))
import Proarrow.Object (Obj, obj, src, tgt)
import Proarrow.Functor (Functor(..), Prelude (..))
import Proarrow.Object.BinaryProduct ()
import Proarrow.Object.BinaryCoproduct (COPROD(..), Coprod (..), mkCoprod)
import Proarrow.Category.Instance.Subcategory (SUBCAT(..), Sub (..))
import Proarrow.Category.Instance.Kleisli (KLEISLI(..), Kleisli(..))
import Proarrow.Profunctor.Star (Star(..))
import Proarrow.Category.Instance.Product ((:**:) (..))


class (Monoidal m, CategoryOf k) => MonoidalAction m k where
  type Act (p :: m) (x :: k) :: k
  act :: (p :: m) ~> q -> (x :: k) ~> y -> Act p x ~> Act q y
  unitor :: Ob (x :: k) => Act (Unit :: m) x ~> x
  unitorInv :: Ob (x :: k) => x ~> Act (Unit :: m) x
  multiplicator :: Obj (p :: m) -> Obj (q :: m) -> Obj (x :: k) -> Act p (Act q x) ~> Act (p ** q) x
  multiplicatorInv :: Obj (p :: m) -> Obj (q :: m) -> Obj (x :: k) -> Act (p ** q) x ~> Act p (Act q x)

instance MonoidalAction Type Type where
  type Act p x = p ** x
  act = par
  unitor = leftUnitor obj
  unitorInv = leftUnitorInv obj
  multiplicator = associatorInv
  multiplicatorInv = associator

instance MonoidalAction (COPROD Type) (COPROD Type) where
  type Act p x = p ** x
  act = par
  unitor = leftUnitor obj
  unitorInv = leftUnitorInv obj
  multiplicator = associatorInv
  multiplicatorInv = associator

instance (MonoidalAction n j, MonoidalAction m k) => MonoidalAction (n, m) (j, k) where
  type Act '(p, q) '(x, y) = '(Act p x, Act q y)
  act (p :**: q) (x :**: y) = act p x :**: act q y
  unitor = unitor @n :**: unitor @m
  unitorInv = unitorInv @n :**: unitorInv @m
  multiplicator (p :**: q) (r :**: s) (x :**: y) = multiplicator p r x :**: multiplicator q s y
  multiplicatorInv (p :**: q) (r :**: s) (x :**: y) = multiplicatorInv p r x :**: multiplicatorInv q s y

instance MonoidalAction Type (COPROD Type) where
  type Act (p :: Type) (COPR x :: COPROD Type) = COPR (p ** x)
  l `act` Coprod r = Coprod (l `par` r)
  unitor = Coprod (leftUnitor obj)
  unitorInv = Coprod (leftUnitorInv obj)
  multiplicator p q (Coprod x) = Coprod (associatorInv p q x)
  multiplicatorInv p q (Coprod x) = Coprod (associator p q x)

instance MonoidalAction (COPROD Type) Type where
  type Act (p :: COPROD Type) (x :: Type) = UN COPR (p ** COPR x)
  f@Coprod{} `act` g = getCoprod (f `par` mkCoprod g)
  unitor = getCoprod (leftUnitor obj)
  unitorInv = getCoprod (leftUnitorInv obj)
  multiplicator p@Coprod{} q@Coprod{} x = getCoprod (associatorInv p q (mkCoprod x))
  multiplicatorInv p@Coprod{} q@Coprod{} x = getCoprod (associator p q (mkCoprod x))

instance (MonoidalAction m Type, Monoidal (SUBCAT (ob :: OB m))) => MonoidalAction (SUBCAT (ob :: OB m)) Type where
  type Act (p :: SUBCAT ob) (x :: Type) = Act (UN SUB p) x
  act (Sub f) g = f `act` g
  unitor = unitor @m
  unitorInv = unitorInv @m
  multiplicator (Sub p) (Sub q) = multiplicator p q
  multiplicatorInv (Sub p) (Sub q) = multiplicatorInv p q

instance MonoidalAction (Type -> Type) Type where
  type Act (p :: Type -> Type) (x :: Type) = p x
  act (Nat n) f = n . map f
  unitor = runIdentity
  unitorInv = Identity
  multiplicator _ _ _ = Compose
  multiplicatorInv _ _ _ = getCompose

instance Monad m => MonoidalAction Type (KlCat m) where
  type Act (p :: Type) (KL x :: KlCat m) = KL (p ** x)
  l `act` Kleisli (Star r) = Kleisli (Star (\(p, a) -> map (l p,) (r a)))
  unitor = Kleisli (Star (Prelude . return . unitor @Type))
  unitorInv = Kleisli (Star (Prelude . return . unitorInv @Type))
  multiplicator p q (Kleisli Star{}) = Kleisli (Star (Prelude . return . multiplicator @Type p q obj))
  multiplicatorInv p q (Kleisli Star{}) = Kleisli (Star (Prelude . return . multiplicatorInv @Type p q obj))



class (MonoidalAction m c, MonoidalAction m d, Profunctor p) => Tambara m (p :: PRO c d) where
  tambara :: Obj (x :: m) -> p a b -> p (x `Act` a) (x `Act` b)


data Optic m a b s t where
  Optic :: (MonoidalAction m c, MonoidalAction m d, Ob (a :: c), Ob (b :: d))
        => Obj (x :: m)
        -> s ~> (x `Act` a)
        -> (x `Act` b) ~> t
        -> Optic m a b s t

instance (CategoryOf c, CategoryOf d) => Profunctor (Optic m (a :: c) (b :: d)) where
  dimap l r (Optic x f g) = Optic x (f . l) (r . g)
  r \\ Optic _ f g = r \\ f \\ g

instance (MonoidalAction m c, MonoidalAction m d) => Tambara m (Optic m (a :: c) (b :: d)) where
  tambara x (Optic m f g) = Optic (x `par` m)
    (multiplicator x m (obj @a) . act x f)
    (act x g . multiplicatorInv x m (obj @b))

parallel :: Optic m a b s t -> Optic n c d u v -> Optic (m, n) '(a, c) '(b, d) '(s, u) '(t, v)
parallel (Optic x f g) (Optic y h i) = Optic (x :**: y) (f :**: h) (g :**: i)


type data OPTIC (m :: Kind) (c :: Kind) (d :: Kind) = OPT c d
type family LCat (p :: OPTIC m c d) where LCat (OPT c d) = c
type family RCat (p :: OPTIC m c d) where RCat (OPT c d) = d
type OpticCat :: CAT (OPTIC m c d)
data OpticCat ab st where
  OpticCat :: Optic m a b s t -> OpticCat (OPT a b :: OPTIC m c d) (OPT s t)

instance (MonoidalAction m c, MonoidalAction m d) => Profunctor (OpticCat :: CAT (OPTIC m c d)) where
  dimap = dimapDefault
  r \\ OpticCat (Optic _ f g) = r \\ f \\ g
instance (MonoidalAction m c, MonoidalAction m d) => Promonad (OpticCat :: CAT (OPTIC m c d)) where
  id = OpticCat (prof2ex id)
  OpticCat l@Optic{} . OpticCat r@Optic{} = OpticCat $ prof2ex (ex2prof l . ex2prof r)
instance (MonoidalAction m c, MonoidalAction m d) => CategoryOf (OPTIC m c d) where
  type (~>) = OpticCat
  type Ob a = (a ~ OPT (LCat a) (RCat a), Ob (LCat a), Ob (RCat a))


type ProfOptic m (a :: c) (b :: d) s t = forall p. Tambara m p => p a b -> p s t

ex2prof :: Optic m a b s t -> ProfOptic m a b s t
ex2prof (Optic x l r) = dimap l r . tambara x

prof2ex :: forall {c} {d} m a b s t. (MonoidalAction m c, MonoidalAction m d, Ob a, Ob b) => ProfOptic m (a :: c) (b :: d) (s :: c) (t :: d) -> Optic m a b s t
prof2ex p2p = p2p (Optic (obj @Unit) (unitorInv @m) (unitor @m))


type Lens s t a b = ProfOptic Type a b s t
mkLens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
mkLens sa sbt = ex2prof (Optic (src sa) (\s -> (s, sa s)) (uncurry sbt))

type Prism s t a b = ProfOptic (COPROD Type) (COPR a) (COPR b) (COPR s) (COPR t)
mkPrism :: (s -> Either t a) -> (b -> t) -> Prism s t a b
mkPrism sat bt = ex2prof (Optic (Coprod (tgt bt)) (Coprod sat) (Coprod (either id bt)))

type Traversal s t a b = ProfOptic (Type -> Type) a b s t
traversing :: Traversable f => Traversal (f a) (f b) a b
traversing = ex2prof @(Type -> Type) (Optic obj Prelude getPrelude)

class Monad m => Algebra m a where algebra :: m a -> a
instance Monad m => Algebra m (m a) where algebra = (>>= id)
instance Monad m => Algebra m () where algebra _ = ()
instance (Monad m, Algebra m a, Algebra m b) => Algebra m (a, b) where algebra mab = (algebra (fmap fst mab), algebra (fmap snd mab))

type AlgebraicLens m s t a b = ProfOptic (SUBCAT (Algebra m)) a b s t
mkAlgebraicLens :: forall m s t a b. Monad m => (s -> a) -> (m s -> b -> t) -> AlgebraicLens m s t a b
mkAlgebraicLens v u = ex2prof @(SUBCAT (Algebra m)) (Optic (Sub obj) (\s -> (return @m s, v s)) (uncurry u))



newtype Viewing a (b :: Type) s (t :: Type) = Viewing { getView :: s -> a }
instance Profunctor (Viewing a b) where
  dimap l _ (Viewing f) = Viewing (f . l)
instance Tambara Type (Viewing a b) where
  tambara _ (Viewing f) = Viewing (f . snd)

infixl 8 ^.
(^.) :: s -> (Viewing a b a b -> Viewing a b s t) -> a
(^.) s l = getView (l $ Viewing id) s


data Previewing a (b :: COPROD Type) s (t :: COPROD Type) where
  Previewing :: { getPreview :: s -> Maybe a } -> Previewing (COPR a) (COPR b) (COPR s) (COPR t)
instance Profunctor (Previewing a b) where
  dimap (Coprod l) Coprod{} (Previewing f) = Previewing (f . l)
  r \\ Previewing f = r \\ f
instance Tambara (COPROD Type) (Previewing a b) where
  tambara Coprod{} (Previewing f) = Previewing (either (const Nothing) f)
instance Tambara Type (Previewing a b) where
  tambara _ (Previewing f) = Previewing (f . snd)

infixl 8 ?.
(?.) :: s -> (Previewing (COPR a) (COPR b) (COPR a) (COPR b) -> Previewing (COPR a) (COPR b) (COPR s) (COPR t)) -> Maybe a
(?.) s l = getPreview (l $ Previewing Just) s


newtype Setting a b s t = Setting { getSet :: (a -> b) -> (s -> t) }
instance Profunctor (Setting a b) where
  dimap l r (Setting f) = Setting (\u -> r . f u . l)
instance Tambara Type (Setting a b) where
  tambara _ (Setting f) = Setting (\u (w,x) -> (w , f u x))
instance Tambara (COPROD Type) (Setting a b) where
  tambara Coprod{} (Setting f) = Setting (fmap . f)

infixl 8 .~
(.~) :: (Setting a b a b -> Setting a b s t) -> b -> s -> t
(.~) l b = getSet (l $ Setting id) (const b)


type KlCat m = KLEISLI (Star (Prelude m))
data Updating a b s t where
  Update :: { getUpdate :: b -> s -> m t } -> Updating a (KL b :: KlCat m) s (KL t :: KlCat m)
instance Monad m => Profunctor (Updating a b :: PRO Type (KlCat m)) where
  dimap l (Kleisli (Star r)) (Update u) = Update (\b x -> u b (l x) >>= getPrelude . r)
  r \\ Update u = r \\ u
instance Monad m => Tambara Type (Updating a b :: PRO Type (KlCat m)) where
  tambara _ (Update u) = Update (\b (w, x) -> fmap (w,) (u b x))

mupdate :: Monad m => (Updating a (KL b :: KlCat m) a (KL b :: KlCat m) -> Updating a (KL b :: KlCat m) s (KL t :: KlCat m)) -> b -> s -> m t
mupdate f = getUpdate $ f (Update (\b _ -> return b))


newtype Replacing a b s t = Replace { getReplace :: (a -> b) -> (s -> t) }
instance Profunctor (Replacing a b) where
  dimap l r (Replace f) = Replace (\ab -> r . f ab . l)
instance Tambara Type (Replacing a b) where
  tambara _ (Replace f) = Replace (map . f)
instance Tambara (COPROD Type) (Replacing a b) where
  tambara _ (Replace f) = Replace (map . f)
instance Tambara (Type -> Type) (Replacing a b) where
  tambara Nat{} (Replace f) = Replace (map . f)

infixl 8 %~
(%~) :: (Replacing a b a b -> Replacing a b s t) -> (a -> b) -> (s -> t)
(%~) l = getReplace (l $ Replace id)


newtype Classifying m a b s t = Classifying
  { getClassify :: (Monad m) => m s -> b -> t }
instance Monad m => Profunctor (Classifying m a b) where
  dimap l r (Classifying f) = Classifying (\u -> r . f (fmap l u))
instance Monad m => Tambara (SUBCAT (Algebra m)) (Classifying m a b) where
  tambara Sub{} (Classifying f) = Classifying (\w b -> (algebra (fmap fst w), f (fmap snd w) b))

infixl 8 .?
(.?) :: (Monad m) => (Classifying m a b a b -> Classifying m a b s t) -> b -> m s -> t
(.?) l b ms = getClassify (l $ Classifying (const id)) ms b
