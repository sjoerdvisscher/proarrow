{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE IncoherentInstances #-}

module Proarrow.Category.Monoidal.Optic where

import Data.Bifunctor (bimap)
import Data.Functor.Compose (Compose (..))
import Data.Functor.Identity (Identity (..))
import Data.Kind (Constraint, Type)
import Prelude (Either, Maybe (..), Monad (..), Traversable, const, either, fmap, fst, snd, uncurry, ($), type (~))

import Proarrow.Category.Instance.Kleisli (KLEISLI (..), Kleisli (..))
import Proarrow.Category.Instance.Nat (Nat (..), (!))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Core (CAT, CategoryOf (..), Kind, OB, PRO, Profunctor (..), Promonad (..), UN, dimapDefault, (:~>))
import Proarrow.Functor (Functor (..), Prelude (..))
import Proarrow.Monoid (Monoid (..))
import Proarrow.Object (obj, src, tgt)
import Proarrow.Object.BinaryCoproduct (COPROD (..), Coprod (..))
import Proarrow.Object.BinaryProduct ()
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Day (Day (..), DayUnit (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Star (Star (..))
import Proarrow.Profunctor.Yoneda (Yo (..))

class (Monoidal m, CategoryOf k) => MonoidalAction m k where
  type Act (p :: m) (x :: k) :: k
  act :: (p :: m) ~> q -> (x :: k) ~> y -> Act p x ~> Act q y
  unitor :: Ob (x :: k) => Act (Unit :: m) x ~> x
  unitorInv :: Ob (x :: k) => x ~> Act (Unit :: m) x
  multiplicator :: (Ob (p :: m), Ob (q :: m), Ob (x :: k)) => Act p (Act q x) ~> Act (p ** q) x
  multiplicatorInv :: (Ob (p :: m), Ob (q :: m), Ob (x :: k)) => Act (p ** q) x ~> Act p (Act q x)

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
  unitor = unitor @n :**: unitor @m
  unitorInv = unitorInv @n :**: unitorInv @m
  multiplicator @'(p, q) @'(r, s) @'(x, y) = multiplicator @n @j @p @r @x :**: multiplicator @m @k @q @s @y
  multiplicatorInv @'(p, q) @'(r, s) @'(x, y) = multiplicatorInv @n @j @p @r @x :**: multiplicatorInv @m @k @q @s @y

instance MonoidalAction Type (COPROD Type) where
  type Act (p :: Type) (COPR x :: COPROD Type) = COPR (p ** x)
  l `act` Coprod r = Coprod (l `par` r)
  unitor = Coprod leftUnitor
  unitorInv = Coprod leftUnitorInv
  multiplicator = Coprod associatorInv
  multiplicatorInv = Coprod associator

instance MonoidalAction (COPROD Type) Type where
  type Act (p :: COPROD Type) (x :: Type) = UN COPR (p ** COPR x)
  f@Coprod{} `act` g = unCoprod (f `par` Coprod g)
  unitor = unCoprod leftUnitor
  unitorInv = unCoprod leftUnitorInv
  multiplicator = unCoprod associatorInv
  multiplicatorInv = unCoprod associator

instance (MonoidalAction m k, Monoidal (SUBCAT (ob :: OB m))) => MonoidalAction (SUBCAT (ob :: OB m)) k where
  type Act (p :: SUBCAT ob) (x :: k) = Act (UN SUB p) x
  act (Sub f) g = f `act` g
  unitor = unitor @m
  unitorInv = unitorInv @m
  multiplicator @(SUB p) @(SUB q) @x = multiplicator @_ @_ @p @q @x
  multiplicatorInv @(SUB p) @(SUB q) @x = multiplicatorInv @_ @_ @p @q @x

instance MonoidalAction (Type -> Type) Type where
  type Act (p :: Type -> Type) (x :: Type) = p x
  act (Nat n) f = n . map f
  unitor = runIdentity
  unitorInv = Identity
  multiplicator = Compose
  multiplicatorInv = getCompose

instance (Monad m) => MonoidalAction Type (KlCat m) where
  type Act (p :: Type) (KL x :: KlCat m) = KL (p ** x)
  l `act` Kleisli (Star r) = Kleisli (Star (\(p, a) -> map (l p,) (r a)))
  unitor = Kleisli (Star (Prelude . return . unitor @Type))
  unitorInv = Kleisli (Star (Prelude . return . unitorInv @Type))
  multiplicator = Kleisli (Star (Prelude . return . multiplicator @Type))
  multiplicatorInv = Kleisli (Star (Prelude . return . multiplicatorInv @Type))

-- | "Day convolaction"
data DayAct w p a b where
  DayAct :: forall c d e f w p a b. a ~> Act c e -> w c d -> p e f -> Act d f ~> b -> DayAct w p a b

instance (Profunctor w, Profunctor p) => Profunctor (DayAct (w :: PRO m m') (p :: PRO c d)) where
  dimap l r (DayAct f w p g) = DayAct (f . l) w p (r . g)
  r \\ DayAct f _ _ g = r \\ f \\ g

instance (MonoidalAction m c, MonoidalAction m' d) => MonoidalAction (PRO m m') (PRO c d) where
  type Act (w :: PRO m m') (p :: PRO c d) = DayAct w p
  act (Prof n) (Prof m) = Prof \(DayAct f w p g) -> DayAct f (n w) (m p) g
  unitor = Prof \(DayAct f (DayUnit a b) p g) -> dimap (unitor @m . act a (src p) . f) (g . act b (tgt p) . unitorInv @m') p \\ p
  unitorInv = Prof \p -> DayAct (unitorInv @m) (DayUnit par0 par0) p (unitor @m') \\ p
  multiplicator = Prof \(DayAct @c1 @d1 f w (DayAct @c2 @d2 @e2 @f2 f' w' p g') g) ->
    let c1 = src w; d1 = tgt w
    in DayAct
        (multiplicator @_ @_ @c1 @c2 @e2 . act c1 f' . f)
        (Day id w w' id)
        p
        (g . act d1 g' . multiplicatorInv @_ @_ @d1 @d2 @f2)
        \\ (src w `par` src w')
        \\ (tgt w `par` tgt w')
        \\ w \\ w' \\ p
  multiplicatorInv = Prof \(DayAct @_ @_ @e1 @f1 f (Day @c2 @d2 @e2 @f2 f' w w' g') p g) ->
    let e2 = src w'; f2 = tgt w'; e1 = src p; f1 = tgt p
    in DayAct
        (multiplicatorInv @_ @_ @c2 @e2 @e1 . act f' e1 . f)
        w
        (DayAct id w' p id)
        (g . act g' f1 . multiplicator @_ @_ @d2 @f2 @f1)
        \\ (e2 `act` e1)
        \\ (f2 `act` f1)
        \\ w \\ w' \\ p

memptyAct :: forall m c (a :: m) (n :: c). (MonoidalAction m c, Monoid a, Ob n) => n ~> Act a n
memptyAct = act @m @c (mempty @a) (obj @n) . unitorInv @m

mappendAct :: forall m c (a :: m) (n :: c). (MonoidalAction m c, Monoid a, Ob n) => Act a (Act a n) ~> Act a n
mappendAct = act @m @c (mappend @a) (obj @n) . multiplicator @m @c @a @a @n

type ModuleObject :: forall {m} {c}. m -> c -> Constraint
class (MonoidalAction m c, Monoid a, Ob n) => ModuleObject (a :: m) (n :: c) where
  action :: Act a n ~> n

class
  (Monoid w, MonoidalAction m c, MonoidalAction m' d, Profunctor p, ModuleObject w p) =>
  Tambara (w :: PRO m m') (p :: PRO c d)
instance
  (Monoid w, MonoidalAction m c, MonoidalAction m' d, Profunctor p, ModuleObject w p)
  => Tambara (w :: PRO m m') (p :: PRO c d)

instance (MonoidalAction m c) => ModuleObject (Id :: PRO m m) (Id :: PRO c c) where
  action = Prof \(DayAct l (Id f) (Id g) r) -> Id (r . act f g . l)

instance (MonoidalProfunctor w1, MonoidalProfunctor w2, Tambara w1 p1, Tambara w2 p2) => ModuleObject (w1 :.: w2) (p1 :.: p2) where
  action = Prof \(DayAct l (w1 :.: w2) (p1 :.: p2) r) ->
    unProf (action @w1) (DayAct l w1 p1 (tgt w1 `act` tgt p1))
      :.: unProf (action @w2) (DayAct (src w2 `act` src p2) w2 p2 r)

type Optic :: PRO m m' -> c -> d -> c -> d -> Type
data Optic w a b s t where
  Optic
    :: forall {c} {d} a b s t m m' w (x :: m) (x' :: m')
     . (Ob (a :: c), Ob (b :: d))
    => s ~> (x `Act` a)
    -> w x x'
    -> (x' `Act` b) ~> t
    -> Optic (w :: PRO m m') a b s t

type IsOptic (w :: PRO m m') c d = (MonoidalProfunctor w, MonoidalAction m c, MonoidalAction m' d)

opticAsDayAct :: (CategoryOf c, CategoryOf d) => (Optic w a b :: PRO c d) :~> DayAct w (Yo a b)
opticAsDayAct (Optic f w g) = DayAct f w (Yo id id) g

dayActAsOptic :: (IsOptic w c d) => DayAct w (Yo a b :: PRO c d) :~> Optic w a b
dayActAsOptic (DayAct f w (Yo l r) g) = Optic (act (src w) l . f) w (g . act (tgt w) r) \\ l \\ r

instance (CategoryOf c, CategoryOf d) => Profunctor (Optic w a b :: PRO c d) where
  dimap l r (Optic f w g) = Optic (f . l) w (r . g)
  r \\ Optic f _ g = r \\ f \\ g

instance (IsOptic w c d) => ModuleObject (w :: PRO m m') (Optic w a b :: PRO c d) where
  action = Prof dayActAsOptic . mappendAct @(PRO m m') @(PRO c d) . act (obj @w) (Prof opticAsDayAct)

parallel :: Optic w a b s t -> Optic w' c d u v -> Optic (w :**: w') '(a, c) '(b, d) '(s, u) '(t, v)
parallel (Optic f w g) (Optic h w' i) = Optic (f :**: h) (w :**: w') (g :**: i)

type data OPTIC (w :: PRO m m') (c :: Kind) (d :: Kind) = OPT c d
type family LCat (p :: OPTIC w c d) where
  LCat (OPT c d) = c
type family RCat (p :: OPTIC w c d) where
  RCat (OPT c d) = d
type OpticCat :: CAT (OPTIC w c d)
data OpticCat ab st where
  OpticCat :: Optic w a b s t -> OpticCat (OPT a b :: OPTIC w c d) (OPT s t)

instance (IsOptic w c d) => Profunctor (OpticCat :: CAT (OPTIC w c d)) where
  dimap = dimapDefault
  r \\ OpticCat (Optic f _ g) = r \\ f \\ g
instance (IsOptic w c d) => Promonad (OpticCat :: CAT (OPTIC w c d)) where
  id = OpticCat (prof2ex id)
  OpticCat l@Optic{} . OpticCat r@Optic{} = OpticCat $ prof2ex (ex2prof l . ex2prof r)
instance (IsOptic w c d) => CategoryOf (OPTIC w c d) where
  type (~>) = OpticCat
  type Ob a = (a ~ OPT (LCat a) (RCat a), Ob (LCat a), Ob (RCat a))

type ProfOptic w a b s t = forall p. (Tambara w p) => p a b -> p s t
type MixedOptic m a b s t = ProfOptic ((~>) @m) a b s t

ex2prof :: forall w a b s t. Optic w a b s t -> ProfOptic w a b s t
ex2prof (Optic l w r) p = unProf (action @w) (DayAct l w p r) \\ w \\ p

prof2ex
  :: forall {c} {d} m m' w a b s t
   . (MonoidalProfunctor w, MonoidalAction m c, MonoidalAction m' d, Ob a, Ob b)
  => ProfOptic (w :: PRO m m') (a :: c) (b :: d) (s :: c) (t :: d)
  -> Optic w a b s t
prof2ex p2p = p2p (Optic (unitorInv @m) par0 (unitor @m'))

type Lens s t a b = MixedOptic Type a b s t
mkLens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
mkLens sa sbt = ex2prof (Optic (\s -> (s, sa s)) (src sa) (uncurry sbt))

type Prism s t a b = MixedOptic (COPROD Type) (COPR a) (COPR b) (COPR s) (COPR t)
mkPrism :: (s -> Either t a) -> (b -> t) -> Prism s t a b
mkPrism sat bt = ex2prof (Optic (Coprod sat) (Coprod (tgt bt)) (Coprod (either id bt)))

type Traversal s t a b = MixedOptic (Type -> Type) a b s t
traversing :: (Traversable f) => Traversal (f a) (f b) a b
traversing = ex2prof @((~>) @(Type -> Type)) (Optic Prelude id unPrelude)

class (Monad m) => Algebra m a where algebra :: m a -> a
instance (Monad m) => Algebra m (m a) where algebra = (>>= id)
instance (Monad m) => Algebra m () where algebra _ = ()
instance (Monad m, Algebra m a, Algebra m b) => Algebra m (a, b) where
  algebra mab = (algebra (fmap fst mab), algebra (fmap snd mab))

type AlgebraicLens m s t a b = MixedOptic (SUBCAT (Algebra m)) a b s t
mkAlgebraicLens :: forall m s t a b. (Monad m) => (s -> a) -> (m s -> b -> t) -> AlgebraicLens m s t a b
mkAlgebraicLens v u = ex2prof @((~>) @(SUBCAT (Algebra m))) (Optic (\s -> (return @m s, v s)) (Sub obj) (uncurry u))

newtype Viewing a (b :: Type) s (t :: Type) = Viewing {unView :: s -> a}
instance Profunctor (Viewing a b) where
  dimap l _ (Viewing f) = Viewing (f . l)
instance ModuleObject (->) (Viewing a b) where
  action = Prof \(DayAct l _ (Viewing f) _) -> Viewing (f . snd . l)

infixl 8 ^.
(^.) :: s -> (Viewing a b a b -> Viewing a b s t) -> a
(^.) s l = unView (l $ Viewing id) s

data Previewing a (b :: COPROD Type) s (t :: COPROD Type) where
  Previewing :: {unPreview :: s -> Maybe a} -> Previewing (COPR a) (COPR b) (COPR s) (COPR t)
instance Profunctor (Previewing a b) where
  dimap (Coprod l) Coprod{} (Previewing f) = Previewing (f . l)
  r \\ Previewing f = r \\ f
instance ModuleObject (Coprod (->)) (Previewing a b) where
  action = Prof \(DayAct (Coprod l) _ (Previewing f) Coprod{}) -> Previewing (either (const Nothing) f . l)
instance ModuleObject (->) (Previewing a b) where
  action = Prof \(DayAct (Coprod l) _ (Previewing f) Coprod{}) -> Previewing (f . snd . l)

infixl 8 ?.
(?.)
  :: s -> (Previewing (COPR a) (COPR b) (COPR a) (COPR b) -> Previewing (COPR a) (COPR b) (COPR s) (COPR t)) -> Maybe a
(?.) s l = unPreview (l $ Previewing Just) s

newtype Setting a b s t = Setting {unSet :: (a -> b) -> (s -> t)}
instance Profunctor (Setting a b) where
  dimap l r (Setting f) = Setting (\u -> r . f u . l)
instance ModuleObject (->) (Setting a b) where
  action = Prof \(DayAct l w (Setting f) r) -> Setting (\u -> r . bimap w (f u) . l)
instance ModuleObject (Coprod (->)) (Setting a b) where
  action = Prof \(DayAct l (Coprod w) (Setting f) r) -> Setting (\u -> r . bimap w (f u) . l)

infixl 8 .~
(.~) :: (Setting a b a b -> Setting a b s t) -> b -> s -> t
(.~) l b = unSet (l $ Setting id) (const b)

type KlCat m = KLEISLI (Star (Prelude m))
data Updating a b s t where
  Update :: {unUpdate :: b -> s -> m t} -> Updating a (KL b :: KlCat m) s (KL t :: KlCat m)
instance (Monad m) => Profunctor (Updating a b :: PRO Type (KlCat m)) where
  dimap l (Kleisli (Star r)) (Update u) = Update (\b x -> u b (l x) >>= unPrelude . r)
  r \\ Update u = r \\ u
instance (Monad m) => ModuleObject (->) (Updating a b :: PRO Type (KlCat m)) where
  action = Prof \(DayAct l f (Update u) (Kleisli (Star r))) -> Update (\b a -> do let {(c, e) = l a; d = f c}; t <- u b e; unPrelude (r (d, t)))

mupdate
  :: (Monad m)
  => (Updating a (KL b :: KlCat m) a (KL b :: KlCat m) -> Updating a (KL b :: KlCat m) s (KL t :: KlCat m))
  -> b
  -> s
  -> m t
mupdate f = unUpdate $ f (Update (\b _ -> return b))

newtype Replacing a b s t = Replace {unReplace :: (a -> b) -> (s -> t)}
instance Profunctor (Replacing a b) where
  dimap l r (Replace f) = Replace (\ab -> r . f ab . l)
instance ModuleObject (->) (Replacing a b) where
  action = Prof \(DayAct l w (Replace f) r) -> Replace (\u -> r . bimap w (f u) . l)
instance ModuleObject (Coprod (->)) (Replacing a b) where
  action = Prof \(DayAct l (Coprod w) (Replace f) r) -> Replace (\u -> r . bimap w (f u) . l)
instance ModuleObject (Nat :: CAT (Type -> Type)) (Replacing a b) where
  action = Prof \(DayAct l w (Replace f) r) -> Replace (\g -> r . (w ! f g) . l)

infixl 8 %~
(%~) :: (Replacing a b a b -> Replacing a b s t) -> (a -> b) -> (s -> t)
(%~) l = unReplace (l $ Replace id)

newtype Classifying m a b s t = Classifying
  {unClassify :: (Monad m) => m s -> b -> t}
instance (Monad m) => Profunctor (Classifying m a b) where
  dimap l r (Classifying f) = Classifying (\u -> r . f (fmap l u))
instance (Monad m) => ModuleObject (Sub (->) :: CAT (SUBCAT (Algebra m))) (Classifying m a b) where
  action = Prof \(DayAct l (Sub w) (Classifying f) r) -> Classifying (\(fmap l -> m) b -> r (algebra (fmap (w . fst) m), f (fmap snd m) b))

infixl 8 .?
(.?) :: (Monad m) => (Classifying m a b a b -> Classifying m a b s t) -> b -> m s -> t
(.?) l b ms = unClassify (l $ Classifying (const id)) ms b
