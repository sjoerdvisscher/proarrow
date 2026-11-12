-- | A promonad transformer that keeps base morphisms separate from effects.
-- Pure composition and tensor stay in the base category; maps around an effect
-- accumulate in 'Coyoneda' until effects meet or 'lowerWithPure' interprets it.
-- Use @KLEISLI (WithPure p)@ as a category that preserves pure routing.
-- Its tensor has the same compatibility requirements with promonad composition
-- as that of @KLEISLI p@; ordered effects keep their original order.
module Proarrow.Promonad.Pure where

import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Action (actHom)
import Proarrow.Category.Monoidal.Strength (Strong (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), arr, lmap, obj, (:~>))
import Proarrow.Functor (Functor (..))
import Proarrow.Object (pattern Objs)
import Proarrow.Profunctor.Instance.Coyoneda (Coyoneda (..), unCoyoneda)

-- | A base morphism, or an effect with accumulated input and output maps.
-- Equality of interpretations, rather than constructor equality, identifies
-- arrows with the same meaning in the underlying promonad.
type WithPure :: CAT k -> CAT k
data WithPure p a b where
  Pure :: a ~> b -> WithPure p a b
  Effect :: Coyoneda p a b -> WithPure p a b

-- | Embed an effect without interpreting it.
liftWithPure :: (Profunctor p) => p :~> WithPure p
liftWithPure p@Objs = Effect (Coyoneda id id p)

-- | Interpret the accumulated maps and effects in the underlying promonad.
-- Lower once and retain the resulting arrow for repeated execution. It sends
-- @Pure f@ to @arr f@ and satisfies @lowerWithPure . liftWithPure = id@.
lowerWithPure :: (Promonad p) => WithPure p :~> p
lowerWithPure (Pure f) = arr f
lowerWithPure (Effect p) = unCoyoneda p

instance (CategoryOf k) => Profunctor (WithPure (p :: CAT k)) where
  dimap l r (Pure f) = Pure (r . f . l)
  dimap l r (Effect (Coyoneda f g p)) = Effect (Coyoneda (f . l) (r . g) p)
  r \\ Pure f = r \\ f
  r \\ Effect (Coyoneda f g _) = r \\ f \\ g

instance (Promonad p) => Promonad (WithPure p) where
  id = Pure id
  Pure g . Pure f = Pure (g . f)
  Pure g . Effect (Coyoneda f h p) = Effect (Coyoneda f (g . h) p)
  Effect (Coyoneda f h p) . Pure g = Effect (Coyoneda (f . g) h p)
  Effect (Coyoneda h i q) . Effect (Coyoneda f g p) =
    Effect (Coyoneda f i (lmap (h . g) q . p))

instance (Promonad p, MonoidalProfunctor p) => MonoidalProfunctor (WithPure p) where
  one = Pure one
  (**) :: forall a b c d. WithPure p a b -> WithPure p c d -> WithPure p (a ** c) (b ** d)
  Pure f ** Pure g = Pure (f ** g)
  Pure f@Objs ** Effect (Coyoneda l r p@Objs) =
    Effect (Coyoneda (f ** l) (obj @b ** r) (id @p @b ** p))
  Effect (Coyoneda l r p@Objs) ** Pure f@Objs =
    Effect (Coyoneda (l ** f) (r ** obj @d) (p ** id @p @d))
  Effect (Coyoneda f g p) ** Effect (Coyoneda h i q) =
    Effect (Coyoneda (f ** h) (g ** i) (p ** q))

instance (Strong t p) => Strong t (WithPure p) where
  act @a (Pure f) = Pure (actHom @t (obj @a) f)
  act @a (Effect (Coyoneda f g p)) =
    Effect (Coyoneda (actHom @t (obj @a) f) (actHom @t (obj @a) g) (act @t @p @a p))

instance Functor WithPure where
  map (Prof n) = Prof \case
    Pure f -> Pure f
    Effect (Coyoneda f g p) -> Effect (Coyoneda f g (n p))
