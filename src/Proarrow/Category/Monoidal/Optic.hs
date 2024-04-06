{-# LANGUAGE AllowAmbiguousTypes, IncoherentInstances #-}
module Proarrow.Category.Monoidal.Optic where

import Data.Kind (Constraint, Type)
import Data.Bifunctor (bimap)
import Data.Functor.Identity (Identity (..))
import Data.Functor.Compose (Compose (..))
import Prelude (uncurry, Either, either, fst, snd, ($), Maybe (..), const, Traversable, Monad (..), fmap)

import Proarrow.Core (CategoryOf (..), PRO, Profunctor (..), Promonad (..), UN, OB, Kind, CAT, dimapDefault, (:~>))
import Proarrow.Category.Monoidal (Monoidal(..), MonoidalProfunctor (..))
import Proarrow.Category.Instance.Nat (Nat (..))
import Proarrow.Functor (Functor(..), Prelude (..))
import Proarrow.Object (Obj, obj, src, tgt)
import Proarrow.Object.BinaryCoproduct (COPROD(..), Coprod (..), mkCoprod)
import Proarrow.Object.BinaryProduct ()
import Proarrow.Category.Instance.Sub (SUBCAT(..), Sub (..))
import Proarrow.Category.Instance.Kleisli (KLEISLI(..), Kleisli(..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Profunctor.Day (Day(..), DayUnit (..))
import Proarrow.Profunctor.Star (Star(..))
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Monoid (Monoid)
import Proarrow.Profunctor.Yoneda (Yo (..))


class (Monoidal m, CategoryOf k) => MonoidalAction m k where
  type Act (p :: m) (x :: k) :: k
  act :: (p :: m) ~> q -> (x :: k) ~> y -> Act p x ~> Act q y
  unitor :: Obj (x :: k) -> Act (Unit :: m) x ~> x
  unitorInv :: Obj (x :: k) -> x ~> Act (Unit :: m) x
  multiplicator :: Obj (p :: m) -> Obj (q :: m) -> Obj (x :: k) -> Act p (Act q x) ~> Act (p ** q) x
  multiplicatorInv :: Obj (p :: m) -> Obj (q :: m) -> Obj (x :: k) -> Act (p ** q) x ~> Act p (Act q x)

instance MonoidalAction Type Type where
  type Act p x = p ** x
  act = par
  unitor = leftUnitor
  unitorInv = leftUnitorInv
  multiplicator = associatorInv
  multiplicatorInv = associator

instance MonoidalAction (COPROD Type) (COPROD Type) where
  type Act p x = p ** x
  act = par
  unitor = leftUnitor
  unitorInv = leftUnitorInv
  multiplicator = associatorInv
  multiplicatorInv = associator

instance (MonoidalAction n j, MonoidalAction m k) => MonoidalAction (n, m) (j, k) where
  type Act '(p, q) '(x, y) = '(Act p x, Act q y)
  act (p :**: q) (x :**: y) = act p x :**: act q y
  unitor (x :**: y) = unitor @n x :**: unitor @m y
  unitorInv (x :**: y) = unitorInv @n x :**: unitorInv @m y
  multiplicator (p :**: q) (r :**: s) (x :**: y) = multiplicator p r x :**: multiplicator q s y
  multiplicatorInv (p :**: q) (r :**: s) (x :**: y) = multiplicatorInv p r x :**: multiplicatorInv q s y

instance MonoidalAction Type (COPROD Type) where
  type Act (p :: Type) (COPR x :: COPROD Type) = COPR (p ** x)
  l `act` Coprod r = Coprod (l `par` r)
  unitor (Coprod x) = Coprod (leftUnitor x)
  unitorInv (Coprod x) = Coprod (leftUnitorInv x)
  multiplicator p q (Coprod x) = Coprod (associatorInv p q x)
  multiplicatorInv p q (Coprod x) = Coprod (associator p q x)

instance MonoidalAction (COPROD Type) Type where
  type Act (p :: COPROD Type) (x :: Type) = UN COPR (p ** COPR x)
  f@Coprod{} `act` g = getCoprod (f `par` mkCoprod g)
  unitor x = getCoprod (leftUnitor (Coprod x))
  unitorInv x = getCoprod (leftUnitorInv (Coprod x))
  multiplicator p@Coprod{} q@Coprod{} x = getCoprod (associatorInv p q (mkCoprod x))
  multiplicatorInv p@Coprod{} q@Coprod{} x = getCoprod (associator p q (mkCoprod x))

instance (MonoidalAction m k, Monoidal (SUBCAT (ob :: OB m))) => MonoidalAction (SUBCAT (ob :: OB m)) k where
  type Act (p :: SUBCAT ob) (x :: k) = Act (UN SUB p) x
  act (Sub f) g = f `act` g
  unitor = unitor @m
  unitorInv = unitorInv @m
  multiplicator (Sub p) (Sub q) = multiplicator p q
  multiplicatorInv (Sub p) (Sub q) = multiplicatorInv p q

instance MonoidalAction (Type -> Type) Type where
  type Act (p :: Type -> Type) (x :: Type) = p x
  act (Nat n) f = n . map f
  unitor _ = runIdentity
  unitorInv _ = Identity
  multiplicator _ _ _ = Compose
  multiplicatorInv _ _ _ = getCompose

instance Monad m => MonoidalAction Type (KlCat m) where
  type Act (p :: Type) (KL x :: KlCat m) = KL (p ** x)
  l `act` Kleisli (Star r) = Kleisli (Star (\(p, a) -> map (l p,) (r a)))
  unitor (Kleisli (Star f)) = Kleisli (Star (Prelude . return . unitor @Type (src f)))
  unitorInv (Kleisli (Star f)) = Kleisli (Star (Prelude . return . unitorInv @Type (src f)))
  multiplicator p q (Kleisli (Star f)) = Kleisli (Star (Prelude . return . multiplicator @Type p q (src f)))
  multiplicatorInv p q (Kleisli (Star f)) = Kleisli (Star (Prelude . return . multiplicatorInv @Type p q (src f)))



-- | "Day convolaction"
data DayAct w p a b where
  DayAct :: forall w p a b c d e f. a ~> Act c e -> w c d -> p e f -> Act d f ~> b -> DayAct w p a b

instance (Profunctor w, Profunctor p) => Profunctor (DayAct (w :: PRO m m') (p :: PRO c d)) where
  dimap l r (DayAct f w p g) = DayAct (f . l) w p (r . g)
  r \\ DayAct f _ _ g = r \\ f \\ g

instance (MonoidalAction m c, MonoidalAction m' d) => MonoidalAction (PRO m m') (PRO c d) where
  type Act (w :: PRO m m') (p :: PRO c d) = DayAct w p
  act (Prof n) (Prof m) = Prof \(DayAct f w p g) -> DayAct f (n w) (m p) g
  unitor Prof{} = Prof \(DayAct f (DayUnit a b) p g) -> dimap (unitor @m (src p) . act a (src p) . f) (g . act b (tgt p) . unitorInv @m' (tgt p)) p \\ p
  unitorInv Prof{} = Prof \p -> DayAct (unitorInv @m (src p)) (DayUnit id id) p (unitor @m' (tgt p)) \\ p
  multiplicator Prof{} Prof{} Prof{} = Prof \(DayAct f w (DayAct f' w' p g') g) ->
    let c1 = src w; c2 = src w'; d1 = tgt w; d2 = tgt w'
    in DayAct
      (multiplicator c1 c2 (src p) . act c1 f' . f)
      (Day id w w' id)
      p
      (g . act d1 g' . multiplicatorInv d1 d2 (tgt p))
    \\ (c1 `par` c2) \\ (d1 `par` d2)
  multiplicatorInv Prof{} Prof{} Prof{} = Prof \(DayAct f (Day f' w w' g') p g) ->
    let c1 = src w; c2 = src w'; d1 = tgt w; d2 = tgt w'; e = src p; e' = tgt p
    in DayAct
      (multiplicatorInv c1 c2 e . act f' e . f)
      w
      (DayAct id w' p id)
      (g . act g' e' . multiplicator d1 d2 e')
    \\ (c2 `act` e) \\ (d2 `act` e')


type ModuleObject :: forall {m} {c}. m -> c -> Constraint
class (MonoidalAction m c, Monoid a, Ob n) => ModuleObject (a :: m) (n :: c) where
  action :: Act a n ~> n


class (MonoidalProfunctor w, MonoidalAction m c, MonoidalAction m' d, Profunctor p) => Tambara (w :: PRO m m') (p :: PRO c d) where
  tambara :: w x x' -> p a b -> p (x `Act` a) (x' `Act` b)

instance (Profunctor p, Tambara w p) => ModuleObject w p where
  action = Prof \(DayAct f w p g) -> dimap f g $ tambara w p

data Optic w a b s t where
  Optic :: forall {c} {d} a b s t m m' w (x :: m) (x' :: m')
        . (Ob (a :: c), Ob (b :: d))
        => s ~> (x `Act` a)
        -> w x x'
        -> (x' `Act` b) ~> t
        -> Optic (w :: PRO m m') a b s t

opticAsDayAct :: (CategoryOf c, CategoryOf d) => Optic w (a :: c) (b :: d) :~> DayAct w (Yo a b)
opticAsDayAct (Optic f w g) = DayAct f w (Yo id id) g

dayActAsOptic
  :: (MonoidalAction m c, MonoidalAction m' d, Profunctor (w :: PRO m m'))
  => DayAct w (Yo (a :: c) (b :: d)) :~> Optic w a b
dayActAsOptic (DayAct f w (Yo l r) g) = Optic (act (src w) l . f) w (g . act (tgt w) r) \\ l \\ r

instance (CategoryOf c, CategoryOf d) => Profunctor (Optic w (a :: c) (b :: d)) where
  dimap l r (Optic f w g) = Optic (f . l) w (r . g)
  r \\ Optic f _ g = r \\ f \\ g

instance (MonoidalProfunctor w, MonoidalAction m c, MonoidalAction m' d) => Tambara (w :: PRO m m') (Optic w (a :: c) (b :: d)) where
  tambara w (Optic f w' g) = Optic
    (multiplicator (src w) (src w') (obj @a) . act (src w) f)
    (lift2 w w')
    (act (tgt w) g . multiplicatorInv (tgt w) (tgt w') (obj @b))

parallel :: Optic w a b s t -> Optic w' c d u v -> Optic (w :**: w') '(a, c) '(b, d) '(s, u) '(t, v)
parallel (Optic f w g) (Optic h w' i) = Optic (f :**: h) (w :**: w') (g :**: i)


type data OPTIC (w :: PRO m m') (c :: Kind) (d :: Kind) = OPT c d
type family LCat (p :: OPTIC w c d) where LCat (OPT c d) = c
type family RCat (p :: OPTIC w c d) where RCat (OPT c d) = d
type OpticCat :: CAT (OPTIC w c d)
data OpticCat ab st where
  OpticCat :: Optic w a b s t -> OpticCat (OPT a b :: OPTIC w c d) (OPT s t)

instance (MonoidalProfunctor w, MonoidalAction m c, MonoidalAction m' d) => Profunctor (OpticCat :: CAT (OPTIC (w :: PRO m m') c d)) where
  dimap = dimapDefault
  r \\ OpticCat (Optic f _ g) = r \\ f \\ g
instance (MonoidalProfunctor w, MonoidalAction m c, MonoidalAction m' d) => Promonad (OpticCat :: CAT (OPTIC (w :: PRO m m') c d)) where
  id = OpticCat (prof2ex id)
  OpticCat l@Optic{} . OpticCat r@Optic{} = OpticCat $ prof2ex (ex2prof l . ex2prof r)
instance (MonoidalProfunctor w, MonoidalAction m c, MonoidalAction m' d) => CategoryOf (OPTIC (w :: PRO m m') c d) where
  type (~>) = OpticCat
  type Ob a = (a ~ OPT (LCat a) (RCat a), Ob (LCat a), Ob (RCat a))


type ProfOptic w a b s t = forall p. Tambara w p => p a b -> p s t
type MixedOptic m a b s t = ProfOptic ((~>) @m) a b s t

ex2prof :: Optic w a b s t -> ProfOptic w a b s t
ex2prof (Optic l w r) = dimap l r . tambara w

prof2ex
  :: forall {c} {d} m m' w a b s t
   . (MonoidalProfunctor w, MonoidalAction m c, MonoidalAction m' d, Ob a, Ob b)
   => ProfOptic (w :: PRO m m') (a :: c) (b :: d) (s :: c) (t :: d)
   -> Optic w a b s t
prof2ex p2p = p2p (Optic (unitorInv @m obj) lift0 (unitor @m' obj))



type Lens s t a b = MixedOptic Type a b s t
mkLens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
mkLens sa sbt = ex2prof (Optic (\s -> (s, sa s)) (src sa) (uncurry sbt))

type Prism s t a b = MixedOptic (COPROD Type) (COPR a) (COPR b) (COPR s) (COPR t)
mkPrism :: (s -> Either t a) -> (b -> t) -> Prism s t a b
mkPrism sat bt = ex2prof (Optic (Coprod sat) (Coprod (tgt bt)) (Coprod (either id bt)))

type Traversal s t a b = MixedOptic (Type -> Type) a b s t
traversing :: Traversable f => Traversal (f a) (f b) a b
traversing = ex2prof @((~>) @(Type -> Type)) (Optic Prelude id getPrelude)

class Monad m => Algebra m a where algebra :: m a -> a
instance Monad m => Algebra m (m a) where algebra = (>>= id)
instance Monad m => Algebra m () where algebra _ = ()
instance (Monad m, Algebra m a, Algebra m b) => Algebra m (a, b) where algebra mab = (algebra (fmap fst mab), algebra (fmap snd mab))

type AlgebraicLens m s t a b = MixedOptic (SUBCAT (Algebra m)) a b s t
mkAlgebraicLens :: forall m s t a b. Monad m => (s -> a) -> (m s -> b -> t) -> AlgebraicLens m s t a b
mkAlgebraicLens v u = ex2prof @((~>) @(SUBCAT (Algebra m))) (Optic (\s -> (return @m s, v s)) (Sub obj) (uncurry u))



newtype Viewing a (b :: Type) s (t :: Type) = Viewing { getView :: s -> a }
instance Profunctor (Viewing a b) where
  dimap l _ (Viewing f) = Viewing (f . l)
instance Tambara (->) (Viewing a b) where
  tambara _ (Viewing f) = Viewing (f . snd)

infixl 8 ^.
(^.) :: s -> (Viewing a b a b -> Viewing a b s t) -> a
(^.) s l = getView (l $ Viewing id) s


data Previewing a (b :: COPROD Type) s (t :: COPROD Type) where
  Previewing :: { getPreview :: s -> Maybe a } -> Previewing (COPR a) (COPR b) (COPR s) (COPR t)
instance Profunctor (Previewing a b) where
  dimap (Coprod l) Coprod{} (Previewing f) = Previewing (f . l)
  r \\ Previewing f = r \\ f
instance Tambara (Coprod :: CAT (COPROD Type)) (Previewing a b) where
  tambara Coprod{} (Previewing f) = Previewing (either (const Nothing) f)
instance Tambara (->) (Previewing a b) where
  tambara _ (Previewing f) = Previewing (f . snd)

infixl 8 ?.
(?.) :: s -> (Previewing (COPR a) (COPR b) (COPR a) (COPR b) -> Previewing (COPR a) (COPR b) (COPR s) (COPR t)) -> Maybe a
(?.) s l = getPreview (l $ Previewing Just) s


newtype Setting a b s t = Setting { getSet :: (a -> b) -> (s -> t) }
instance Profunctor (Setting a b) where
  dimap l r (Setting f) = Setting (\u -> r . f u . l)
instance Tambara (->) (Setting a b) where
  tambara w (Setting f) = Setting (\u (x, a) -> (w x, f u a))
instance Tambara (Coprod :: CAT (COPROD Type)) (Setting a b) where
  tambara (Coprod w) (Setting f) = Setting (bimap w . f)

infixl 8 .~
(.~) :: (Setting a b a b -> Setting a b s t) -> b -> s -> t
(.~) l b = getSet (l $ Setting id) (const b)


type KlCat m = KLEISLI (Star (Prelude m))
data Updating a b s t where
  Update :: { getUpdate :: b -> s -> m t } -> Updating a (KL b :: KlCat m) s (KL t :: KlCat m)
instance Monad m => Profunctor (Updating a b :: PRO Type (KlCat m)) where
  dimap l (Kleisli (Star r)) (Update u) = Update (\b x -> u b (l x) >>= getPrelude . r)
  r \\ Update u = r \\ u
instance Monad m => Tambara (->) (Updating a b :: PRO Type (KlCat m)) where
  tambara f (Update u) = Update (\b (w, x) -> fmap (f w,) (u b x))

mupdate :: Monad m => (Updating a (KL b :: KlCat m) a (KL b :: KlCat m) -> Updating a (KL b :: KlCat m) s (KL t :: KlCat m)) -> b -> s -> m t
mupdate f = getUpdate $ f (Update (\b _ -> return b))


newtype Replacing a b s t = Replace { getReplace :: (a -> b) -> (s -> t) }
instance Profunctor (Replacing a b) where
  dimap l r (Replace f) = Replace (\ab -> r . f ab . l)
instance Tambara (->) (Replacing a b) where
  tambara w (Replace f) = Replace (bimap w . f)
instance Tambara (Coprod :: CAT (COPROD Type)) (Replacing a b) where
  tambara (Coprod w) (Replace f) = Replace (bimap w . f)
instance Tambara (Nat :: CAT (Type -> Type)) (Replacing a b) where
  tambara (Nat w) (Replace f) = Replace \ab -> map (f ab) . w

infixl 8 %~
(%~) :: (Replacing a b a b -> Replacing a b s t) -> (a -> b) -> (s -> t)
(%~) l = getReplace (l $ Replace id)


newtype Classifying m a b s t = Classifying
  { getClassify :: (Monad m) => m s -> b -> t }
instance Monad m => Profunctor (Classifying m a b) where
  dimap l r (Classifying f) = Classifying (\u -> r . f (fmap l u))
instance Monad m => Tambara (Sub :: CAT (SUBCAT (Algebra m))) (Classifying m a b) where
  tambara (Sub w) (Classifying f) = Classifying (\m b -> (algebra (fmap (w . fst) m), f (fmap snd m) b))

infixl 8 .?
(.?) :: (Monad m) => (Classifying m a b a b -> Classifying m a b s t) -> b -> m s -> t
(.?) l b ms = getClassify (l $ Classifying (const id)) ms b
