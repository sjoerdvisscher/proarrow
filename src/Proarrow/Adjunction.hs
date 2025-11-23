{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Adjunction where

import Data.Kind (Constraint)

import Proarrow.Category.Colimit (HasColimits (..), mapColimit)
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Sub (COREP, COREPK, REP, REPK, SUBCAT (..), Sub (..))
import Proarrow.Category.Limit (HasLimits (..), mapLimit)
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), UN, lmap, rmap, (//), (:~>), type (+->))
import Proarrow.Functor (map)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), trivialCorep)
import Proarrow.Profunctor.Costar (Costar (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Representable
  ( CorepStar (..)
  , RepCostar (..)
  , Representable (..)
  , mapCorepStar
  , mapRepCostar
  , trivialRep
  )
import Proarrow.Profunctor.Star (Star (..))
import Proarrow.Promonad (Procomonad (..))

-- | Adjunctions as heteromorphisms.
class (Representable p, Corepresentable p) => Adjunction p

instance (Representable p, Corepresentable p) => Adjunction p

leftAdjunct :: forall p a b. (Adjunction p, Ob a) => (p %% a ~> b) -> a ~> p % b
leftAdjunct = index . cotabulate @p

rightAdjunct :: forall p a b. (Adjunction p, Ob b) => a ~> p % b -> (p %% a ~> b)
rightAdjunct = coindex . tabulate @p

unitRep :: forall p a. (Adjunction p, Ob a) => a ~> p % (p %% a)
unitRep = index (trivialCorep @p)

counitRep :: forall p a. (Adjunction p, Ob a) => p %% (p % a) ~> a
counitRep = coindex (trivialRep @p)

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

type Proadjunction :: forall {j} {k}. j +-> k -> k +-> j -> Constraint

-- | Adjunctions between two profunctors.
class (Profunctor p, Profunctor q) => Proadjunction (p :: j +-> k) (q :: k +-> j) where
  unit :: (Ob a) => (q :.: p) a a -- (~>) :~> q :.: p
  counit :: p :.: q :~> (~>)

instance (Representable f) => Proadjunction f (RepCostar f) where
  unit = trivialCorep :.: trivialRep
  counit (f :.: g) = coindex g . index f

instance (Corepresentable f) => Proadjunction (CorepStar f) f where
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
  extract = counit
  duplicate (p :.: q) = p // case unit of q' :.: p' -> (p :.: q') :.: (p' :.: q)

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

-- | Colimit j -| Limit j
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
  tabulate @(SUB r) (Sub (Op (Prof n))) = LimitAdj (\j -> n (RepCostar (index @r (limit (trivialRep :.: j)))) :.: trivialRep \\ j)
  repMap (Sub n) = Sub (Op (mapRepCostar (mapLimit @j n)))

instance (HasColimits j k) => Corepresentable (LimitAdj (j :: a +-> b) :: REPK a k +-> COREPK b k) where
  type LimitAdj j %% c = REP (CorepStar (Colimit j (UN OP (UN SUB c))))
  cotabulate @(SUB (OP r)) (Sub (Prof n)) = LimitAdj (\j -> trivialCorep :.: n (CorepStar (coindex @r (colimit (j :.: trivialCorep)))) \\ j)
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
  corepMap (Sub (Op n)) = Sub (mapCorepStar (mapColimit @j n))

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