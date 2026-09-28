{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- the identity laws compose with id on purpose
{- HLINT ignore "Redundant id" -}

-- | Promonads as effects: a 'Promonad' ("Proarrow.Core") that is 'Representable' is an ordinary 'Monad'
-- on objects ('return', 'bind'); a 'Promonad' that is 'Corepresentable' is a 'Comonad' ('extract',
-- 'extend'). Also 'Procomonad's and relative (co)monads ('RelativeMonad', 'RelativeComonad'). Concrete
-- promonads live in @Proarrow.Promonad.*@.
module Proarrow.Promonad
  ( Promonad (..)
  , Procomonad (..)
  , Monad
  , return
  , bind
  , Comonad
  , extract
  , extend
  , AsRelative (..)
  , RelativeMonad (..)
  , RelAlgebra
  , RelativeComonad (..)
  , RelCoalgebra
  ) where

import Data.Kind (Constraint)

import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), src, (:~>), type (+->), type (~>))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (Representable (..))
import Proarrow.Tools.Laws (ProLaw (..), ProLaws (..), (=:=), (===))

type Procomonad :: k +-> k -> Constraint
class (Profunctor p) => Procomonad p where
  proextract :: p :~> (~>)
  produplicate :: p :~> p :.: p

-- | 'id' is a unit for composition, which is associative, and both are natural. Elements that
-- start where another one ends are made from the drawn ones with 'lmap' and an arbitrary arrow.
instance ProLaws Promonad where
  proLaws =
    [ ProLaw "left identity" \p _ _ -> p =:= id . p
    , ProLaw "right identity" \p _ _ -> p =:= p . id
    , ProLaw3 "associativity" \ @_ @_ @b @c @d @e p p' p'' mor _ -> do
        g <- mor @b @c "g"
        h <- mor @d @e "h"
        let q = lmap g p'
            r = lmap h p''
        r . (q . p) =:= (r . q) . p
    , ProLaw "id dinaturality" \ @_ @a @_ @c _ mor _ -> do
        g <- mor @c @a "g"
        rmap g id =:= lmap g id
    , ProLaw3 "composition naturality" \ @_ @a @b @c @d @e @f p p' _ mor _ -> do
        k <- mor @b @c "k"
        g <- mor @e @a "g"
        h <- mor @d @f "h"
        let q = lmap k p'
        dimap g h (q . p) =:= rmap h q . lmap g p
    , ProLaw3 "composition dinaturality" \ @_ @_ @b @c p p' _ mor _ -> do
        g <- mor @b @c "g"
        p' . rmap g p =:= lmap g p' . p
    ]

-- | 'proextract' is natural, and extracting either half of 'produplicate' gives back the element.
-- Coassociativity is not an equation between elements: its two sides are composites whose middle
-- objects cannot be compared.
instance ProLaws Procomonad where
  proLaws =
    [ ProLaw "proextract naturality" \ @_ @a @b @c @d p morK morJ -> do
        g <- morK @c @a "g"
        h <- morJ @b @d "h"
        proextract (dimap g h p) === h . proextract p . g
    , ProLaw "left counit" \p _ _ -> case produplicate p of q :.: r -> p =:= lmap (proextract q) r
    , ProLaw "right counit" \p _ _ -> case produplicate p of q :.: r -> p =:= rmap (proextract r) q
    ]

instance (CategoryOf k) => Procomonad (Id :: CAT k) where
  proextract (Id f) = f
  produplicate (Id f) = Id (src f) :.: Id f

-- | A representable promonad is a monad on objects: it acts as the functor @m '%' -@, with
-- 'return' and 'bind'.
type Monad m = (Promonad m, Representable m)

-- | The unit of the monad @m@.
return :: forall m a. (Monad m, Ob a) => a ~> m % a
return = index @m id

-- | Kleisli extension: run a Kleisli arrow under @m@.
bind :: forall m b a. (Monad m, Ob b) => a ~> m % b -> m % a ~> m % b
bind f = index (tabulate @m @b f . (repUniv \\ f))

-- | Dually, a corepresentable promonad is a comonad on objects, acting as @w '%%' -@, with
-- 'extract' and 'extend'.
type Comonad w = (Promonad w, Corepresentable w)

-- | The counit of the comonad @w@.
extract :: forall w a. (Comonad w, Ob a) => w %% a ~> a
extract = coindex @w id

-- | CoKleisli extension: run a coKleisli arrow under @w@.
extend :: forall w a b. (Comonad w, Ob a) => w %% a ~> b -> w %% a ~> w %% b
extend f = coindex ((corepUniv \\ f) . cotabulate @w @a f)

type RelativeMonad :: i +-> k -> k +-> i -> Constraint
class (Representable m, Profunctor j) => RelativeMonad j m where
  relReturn :: (Ob a) => j a (m % a)
  relBind :: (Ob b) => j a (m % b) -> m % a ~> m % b

type RelAlgebra j m a b = j a b -> m % a ~> b

-- | A 'Monad' or 'Comonad' seen as a relative (co)monad along 'Id'.
--
-- The wrapper is needed: a direct @'RelativeMonad' 'Id' m@ instance would unify at @j = 'Id'@ with
-- carrier-specific ones such as the codensity monad's, with neither more specific, so no overlap
-- pragma could order them.
type AsRelative :: (k +-> i) -> k +-> i
newtype AsRelative m a b = AsRelative {unAsRelative :: m a b}
  deriving newtype (Profunctor, Promonad, Representable, Corepresentable)

instance (Monad m) => RelativeMonad Id (AsRelative m) where
  relReturn = Id (return @m)
  relBind @b (Id f) = bind @m @b f

type RelativeComonad :: i +-> k -> k +-> i -> Constraint
class (Corepresentable w, Profunctor j) => RelativeComonad j w where
  relExtract :: (Ob a) => j (w %% a) a
  relExtend :: (Ob a) => j (w %% a) b -> w %% a ~> w %% b

type RelCoalgebra j w a b = j a b -> a ~> w %% b

instance (Comonad w) => RelativeComonad Id (AsRelative w) where
  relExtract = Id (extract @w)
  relExtend @a (Id f) = extend @w @a f
