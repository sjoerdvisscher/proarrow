{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Adjunction where

import Data.Kind (Constraint, Type)
import Prelude (const, type (~))

import Proarrow.Category.Colimit (HasColimits (..))
import Proarrow.Category.Enriched.Thin (Thin, ThinProfunctor)
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Rep (COREP, COREPK, REP, REPK)
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Limit (HasLimits (..), mapLimit)
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), UN, lmap, rmap, (//), (:~>), type (+->))
import Proarrow.Functor (Functor, FunctorForRep, map)
import Proarrow.Object.BinaryCoproduct (Cocartesian, Coprod (..), HasBinaryCoproducts (..))
import Proarrow.Object.BinaryProduct (Cartesian, HasBinaryProducts (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Optic (Iso, iso, re)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Constant (review, view)
import Proarrow.Profunctor.Corepresentable
  ( Corep
  , Corepresentable (..)
  , corepObj
  , cotabulated
  , trivialCorep
  )
import Proarrow.Profunctor.Costar (Costar, pattern Costar)
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Representable
  ( CorepStar (..)
  , Rep
  , RepCostar (..)
  , Representable (..)
  , mapRepCostar
  , repObj
  , tabulated
  , trivialRep
  )
import Proarrow.Profunctor.Star (Star, pattern Star)
import Proarrow.Promonad (Procomonad (..), bind, extend, extract, return)

-- | Adjunctions as heteromorphisms.
class (Representable p, Corepresentable p) => Adjunction p

instance (Representable p, Corepresentable p) => Adjunction p

leftAdjunct :: forall p a b. (Adjunction p, Ob a) => (p %% a ~> b) -> a ~> p % b
leftAdjunct = index . cotabulate @p

rightAdjunct :: forall p a b. (Adjunction p, Ob b) => a ~> p % b -> (p %% a ~> b)
rightAdjunct = coindex . tabulate @p

-- | The isomorphism between @leftAdjunct@ and @rightAdjunct@.
adjuncted
  :: forall p a b a' b'. (Adjunction p, Ob a, Ob b') => Iso (b ~> p % a) (b' ~> p % a') (p %% b ~> a) (p %% b' ~> a')
adjuncted = tabulated @p . re cotabulated

-- | The monad induced by an adjunction as a representable promonad.
type AdjMonad p = p :.: CorepStar p

unitRep :: forall p a. (Adjunction p, Ob a) => a ~> AdjMonad p % a
unitRep = return @(AdjMonad p) @a

bindRep :: forall p a b. (Adjunction p, Ob b) => a ~> AdjMonad p % b -> AdjMonad p % a ~> AdjMonad p % b
bindRep = bind @(AdjMonad p) @b

-- | The comonad induced by an adjunction as a corepresentable promonad.
type AdjComonad p = RepCostar p :.: p

counitRep :: forall p a. (Adjunction p, Ob a) => AdjComonad p %% a ~> a
counitRep = extract @(AdjComonad p) @a

extendRep :: forall p a b. (Adjunction p, Ob a) => (AdjComonad p %% a ~> b) -> AdjComonad p %% a ~> AdjComonad p %% b
extendRep = extend @(AdjComonad p) @a @b

-- | The left adjoint of @((->) a)@ is @(,) a@.
instance Corepresentable (Star ((->) a)) where
  type Star ((->) a) %% b = (a, b)
  cotabulate f = Star \a b -> f (b, a)
  coindex (Star f) (a, b) = f b a
  corepMap = map

-- | The right adjoint of @(,) a@ is @((->) a)@.
instance Representable (Costar ((,) a)) where
  type Costar ((,) a) % b = a -> b
  tabulate f = Costar \(a, b) -> f b a
  index (Costar g) a b = g (b, a)
  repMap = map

class (p % a ~ p %% a, p % (p %% a) ~ p % (p % a), p %% (p % a) ~ p % (p % a)) => SelfAdjointPoint p a
instance (p % a ~ p %% a, p % (p %% a) ~ p % (p % a), p %% (p % a) ~ p % (p % a)) => SelfAdjointPoint p a

-- | Self-adjoint functors
class (forall a. (Ob a) => SelfAdjointPoint p a, Adjunction p) => SelfAdjoint p

instance (forall a. (Ob a) => SelfAdjointPoint p a, Adjunction p) => SelfAdjoint p

-- | Involution functors are self-adjoint functors where the unit and counit form an isomorphism.
class (SelfAdjoint p) => Involution p where
  involuted :: forall a a'. (Ob a, Ob a') => Iso a a' (p % (p % a)) (p % (p % a'))
  involuted = iso (unitRep @p) (counitRep @p)

instance (CategoryOf k) => Involution (Id :: CAT k)

class (p %% a ~ RepCostar p % a, p % (p %% a) ~ p % (RepCostar p % a)) => AmbidextrousEqRep p a
instance (p %% a ~ RepCostar p % a, p % (p %% a) ~ p % (RepCostar p % a)) => AmbidextrousEqRep p a

class (p % a ~ CorepStar p %% a, p %% (p % a) ~ p %% (CorepStar p %% a)) => AmbidextrousEqCorep p a
instance (p % a ~ CorepStar p %% a, p %% (p % a) ~ p %% (CorepStar p %% a)) => AmbidextrousEqCorep p a

class
  ( Adjunction p
  , Representable (RepCostar p)
  , Corepresentable (CorepStar p)
  , forall a. (Ob a) => AmbidextrousEqRep p a
  , forall a. (Ob a) => AmbidextrousEqCorep p a
  ) =>
  Ambidextrous p
instance
  ( Adjunction p
  , Representable (RepCostar p)
  , Corepresentable (CorepStar p)
  , forall a. (Ob a) => AmbidextrousEqRep p a
  , forall a. (Ob a) => AmbidextrousEqCorep p a
  )
  => Ambidextrous p

class (Ambidextrous p) => AdjointEquivalence (p :: j +-> k) where
  unitIso :: (Ob a, Ob a') => Iso a a' (AdjMonad p % a) (AdjMonad p % a')
  unitIso @a @a' = iso (unitRep @p @a) (counitRep @(RepCostar p) @a')
  counitIso :: (Ob a, Ob a') => Iso (AdjComonad p %% a) (AdjComonad p %% a') a a'
  counitIso @a @a' = iso (counitRep @p @a) (unitRep @(CorepStar p) @a')

type GaloisConnection (p :: j +-> k) = (ThinProfunctor p, Thin j, Thin k, Adjunction p)

-- | Adjunctions between two profunctors.
type Proadjunction :: forall {j} {k}. j +-> k -> k +-> j -> Constraint
class (Profunctor p, Profunctor q) => Proadjunction (p :: j +-> k) (q :: k +-> j) where
  unit :: (Ob a) => (q :.: p) a a -- (~>) :~> q :.: p
  counit :: p :.: q :~> (~>)

instance (Representable p) => Proadjunction p (RepCostar p) where
  unit = trivialCorep :.: trivialRep
  counit (f :.: g) = coindex g . index f

instance (Corepresentable p) => Proadjunction (CorepStar p) p where
  unit = trivialCorep :.: trivialRep
  counit (f :.: g) = coindex g . index f

instance (FunctorForRep f) => Proadjunction (Rep f) (Corep f) where
  unit = trivialCorep :.: trivialRep
  counit (f :.: g) = coindex g . index f

instance (Functor f) => Proadjunction (Star f) (Costar f) where
  unit = trivialCorep :.: trivialRep
  counit (f :.: g) = coindex g . index f

instance (Proadjunction l1 r1, Proadjunction l2 r2) => Proadjunction (l1 :.: l2) (r2 :.: r1) where
  unit :: forall a. (Ob a) => ((r2 :.: r1) :.: (l1 :.: l2)) a a
  unit = case unit @l2 @r2 @a of
    r2 :.: l2 ->
      l2 // case unit @l1 @r1 of
        r1 :.: l1 -> (r2 :.: r1) :.: (l1 :.: l2)
  counit ((l1 :.: l2) :.: (r2 :.: r1)) = counit (rmap (counit (l2 :.: r2)) l1 :.: r1)

instance (CategoryOf k) => Proadjunction (Id :: CAT k) Id where
  unit = Id id :.: Id id
  counit (Id f :.: Id g) = g . f

instance (Proadjunction q p) => Proadjunction (Op p) (Op q) where
  unit = case unit @q @p of q :.: p -> Op p :.: Op q
  counit (Op q :.: Op p) = Op (counit (p :.: q))

instance (Proadjunction p q) => Promonad (q :.: p) where
  id = unit
  (q :.: p) . (q' :.: p') = rmap (counit (p' :.: q)) q' :.: p

instance (Proadjunction p q) => Procomonad (p :.: q) where
  proextract = counit
  produplicate (p :.: q) = p // case unit of q' :.: p' -> (p :.: q') :.: (p' :.: q)

-- (~>) :~> Colimit j c :.: r
--    <=>
-- j :~> c :.: r
--    <=>
-- (~>) :~> c :.: Limit j r

type LimitAdj :: (a +-> b) -> REPK a k +-> COREPK b k
data LimitAdj j c r where
  LimitAdj :: (Corepresentable c, Representable r) => (j :~> c :.: r) -> LimitAdj j (COREP c) (REP r)
instance (Profunctor j) => Profunctor (LimitAdj j) where
  dimap (Sub (Op (Prof l))) (Sub (Prof r)) (LimitAdj n) = LimitAdj (\j -> case n j of c :.: d -> l c :.: r d)
  r \\ LimitAdj f = r \\ f

-- | @Colimit j@ ⊣ @Limit j@
instance (HasLimits j k) => Representable (LimitAdj (j :: a +-> b) :: REPK a k +-> COREPK b k) where
  type LimitAdj j % r = COREP (RepCostar (Limit j (UN SUB r)))
  index @c (LimitAdj n) =
    Sub
      ( Op
          ( Prof \(RepCostar @o l) ->
              cotabulate
                ( l
                    . index
                      ( limitUniv @j @k
                          (\(g :.: j) -> case n j of c :.: r -> lmap (coindex c . index g) r)
                          (trivialRep @(CorepStar (UN OP (UN SUB c))) @o)
                      )
                )
          )
      )
  trivialRep @(SUB r) = LimitAdj (\j -> RepCostar (index @r (limit (trivialRep :.: j))) :.: trivialRep \\ j)
  repMap (Sub n) = Sub (Op (mapRepCostar (mapLimit @j n)))

instance (HasColimits j k) => Corepresentable (LimitAdj (j :: a +-> b) :: REPK a k +-> COREPK b k) where
  type LimitAdj j %% c = REP (CorepStar (Colimit j (UN OP (UN SUB c))))
  trivialCorep @(SUB (OP r)) = LimitAdj (\j -> trivialCorep :.: CorepStar (coindex @r (colimit (j :.: trivialCorep))) \\ j)
  coindex @_ @r (LimitAdj n) =
    Sub
      ( Prof \(CorepStar @o l) ->
          tabulate
            ( coindex
                ( colimitUniv @j @k
                    (\(j :.: p) -> case n j of c :.: r -> rmap (coindex p . index r) c)
                    (trivialCorep @(RepCostar (UN SUB r)) @o)
                )
                . l
            )
      )

rightAdjointPreservesLimits
  :: forall {k} {k'} {i} {a} (j :: i +-> a) (p :: k +-> k') (d :: i +-> k)
   . (Adjunction p, Representable d, HasLimits j k, HasLimits j k')
  => Limit j (p :.: d) :~> p :.: Limit j d
rightAdjointPreservesLimits lim =
  trivialCorep @p
    :.: limitUniv @j @k @d
      (\((f' :.: lim') :.: j) -> case limit @j @k' @(p :.: d) (lim' :.: j) of g' :.: d -> lmap (coindex g' . index f') d)
      (trivialRep @(CorepStar p) :.: lim)
    \\ lim

rightAdjointPreservesLimitsInv
  :: forall {k} {k'} {i} {a} (p :: k +-> k') (d :: i +-> k) (j :: i +-> a)
   . (Representable p, Representable d, HasLimits j k, HasLimits j k')
  => p :.: Limit j d :~> Limit j (p :.: d)
rightAdjointPreservesLimitsInv = limitUniv @j @k' @(p :.: d) (\((p :.: lim) :.: j) -> p :.: limit (lim :.: j))

leftAdjointPreservesColimits
  :: forall {k} {k'} {i} {a} (p :: k' +-> k) (d :: k +-> i) (j :: a +-> i)
   . (Adjunction p, Corepresentable d, HasColimits j k, HasColimits j k')
  => Colimit j (d :.: p) :~> Colimit j d :.: p
leftAdjointPreservesColimits colim =
  colimitUniv @j @k @d
    (\(j :.: (colim' :.: g')) -> case colimit @j @k' @(d :.: p) (j :.: colim') of d :.: f' -> rmap (coindex g' . index f') d)
    (colim :.: trivialCorep @(RepCostar p))
    :.: trivialRep @p
    \\ colim

leftAdjointPreservesColimitsInv
  :: forall {k} {k'} {i} {a} (p :: k' +-> k) (d :: k +-> i) (j :: a +-> i)
   . (Corepresentable p, Corepresentable d, HasColimits j k, HasColimits j k')
  => Colimit j d :.: p :~> Colimit j (d :.: p)
leftAdjointPreservesColimitsInv = colimitUniv @j @k' @(d :.: p) (\(j :.: (colim :.: p)) -> colimit (j :.: colim) :.: p)

-- | Preservation of limits and colimits makes the adjunction heteromorphism a distributive profunctor.
newtype Adj p a b = Adj (p a b)
  deriving newtype (Profunctor, Representable, Corepresentable)

instance (Cartesian j, Cartesian k, Adjunction p) => MonoidalProfunctor (Adj p :: j +-> k) where
  par0 = cotabulate terminate \\ corepObj @p @TerminalObject
  Adj @_ @x l `par` Adj @_ @y r =
    withOb2 @_ @x @y
      ( cotabulate
          ( coindex @p @(x ** y) (lmap (fst @_ @x @y) l)
              &&& coindex @p @(x ** y) (lmap (snd @_ @x @y) r)
          )
      )
      \\ l
      \\ r

instance (Cocartesian j, Cocartesian k, Adjunction p) => MonoidalProfunctor (Coprod (Adj p :: j +-> k)) where
  par0 = tabulate initiate \\ repObj @p @InitialObject
  Coprod (Adj @_ @_ @x l) `par` Coprod (Adj @_ @_ @y r) =
    withObCoprod @_ @x @y
      ( Coprod
          ( Adj
              ( tabulate
                  ( index @p @_ @(x || y) (rmap (lft @_ @x @y) l)
                      ||| index @p @_ @(x || y) (rmap (rgt @_ @x @y) r)
                  )
              )
          )
      )
      \\ l
      \\ r

-- | Every adjunction between Hask endofunctors is equivalent to the curry-uncurry adjunction.
haskAdjIsCurryAdj
  :: forall p a b a' b'. (Adjunction (p :: Type +-> Type)) => Iso (p %% () -> a -> b) (p %% () -> a' -> b') (p a b) (p a' b')
haskAdjIsCurryAdj =
  iso (\kab -> tabulate \a -> index @p (cotabulate (`kab` a)) ()) (\p k a -> coindex p (corepMap @p (\() -> a) k))

instance (Adjunction p) => Promonad (Adj p :: Type +-> Type) where
  id = Adj (view (haskAdjIsCurryAdj @p) (const id))
  Adj l . Adj r = Adj (view (haskAdjIsCurryAdj @p) (\k -> review haskAdjIsCurryAdj l k . review haskAdjIsCurryAdj r k))