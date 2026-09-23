{-# OPTIONS_GHC -Wno-orphans #-}

-- | The internal hom of the category of profunctors under the /product/: a @(p ':~>:' q) a b@ is a
-- natural family of maps @p c d -> q c d@ available at @a@\/@b@, making @'PROD' (j +-> k)@ 'Closed'.
-- @j +-> k@ itself is 'Closed' too, but for Day convolution and with a different hom -- see
-- "Proarrow.Profunctor.Instance.Day". The 'PROD' wrapper is what keeps the two apart.
module Proarrow.Profunctor.Instance.Exponential where

import Proarrow.Category.Enriched.Thin
  ( DecidableProfunctor (..)
  , Decision (..)
  , Discrete
  , ThinProfunctor (..)
  , noArrow
  , withEq
  )
import Proarrow.Category.Instance.Bool (BoolLeq)
import Proarrow.Category.Instance.Constraint (reifyExp, (:=>) (..), type (:-) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Sub (IsObProd, SUBCAT (..), Sub (..))
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Core (CategoryOf (..), OB, Profunctor (..), Promonad (..), UN, (//), type (+->))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts, PROD (..), Prod (..))
import Proarrow.Limit.Terminal (HasTerminalObject)
import Proarrow.Profunctor.Instance.Product ((:*:) (..))

data (p :~>: q) a b where
  Exp :: (Ob a, Ob b) => (forall c d. c ~> a -> b ~> d -> p c d -> q c d) -> (p :~>: q) a b

instance (Profunctor p, Profunctor q) => Profunctor (p :~>: q) where
  dimap l r (Exp f) = l // r // Exp \ca bd p -> f (l . ca) (bd . r) p
  r \\ Exp{} = r

instance (CategoryOf j, CategoryOf k) => Closed (PROD (j +-> k)) where
  type p ~~> q = PR (UN PR p :~>: UN PR q)
  withObExp r = r
  curry (Prod (Prof n)) = Prod (Prof \p -> p // Exp \ca bd q -> n (dimap ca bd p :*: q))
  apply = Prod (Prof \(Exp f :*: q) -> f id id q \\ q)
  Prod (Prof m) ^^^ Prod (Prof n) = Prod (Prof \(Exp f) -> Exp \ca bd p -> m (f ca bd (n p)))

-- | That a full subcategory of the profunctors contains the internal homs of its objects, as a
-- class with a single instance, so that it can be the head of the quantified constraint below --
-- 'Proarrow.Category.Instance.Sub.IsObProd' has the same shape for the product.
class (ob (p :~>: q)) => IsObExp (ob :: OB (j +-> k)) p q

instance (ob (p :~>: q)) => IsObExp ob p q

-- | And then the subcategory is closed, with the ambient exponential and nothing of its own --
-- just as its products are the ambient ones. @'Proarrow.Category.Enriched.Finitary.Topos.FINITARY'
-- j k@ is one instance, 'Proarrow.Category.Enriched.Finitary.Sheaf.SHEAVES' another: for the
-- first, a hom-set of natural transformations is finitary; for the second, an internal hom into a
-- sheaf is a sheaf.
instance
  ( CategoryOf j
  , CategoryOf k
  , HasTerminalObject (SUBCAT ob)
  , HasBinaryProducts (SUBCAT ob)
  , -- the product one again, as a constraint: 'apply' needs @ob@ of a product whose left factor is
    -- an internal hom, which no @'Ob' _@ in scope mentions
    forall p q. (ob p, ob q) => IsObProd ob p q
  , forall p q. (ob p, ob q) => IsObExp ob p q
  )
  => Closed (PROD (SUBCAT (ob :: OB (j +-> k))))
  where
  type p ~~> q = PR (SUB (UN SUB (UN PR p) :~>: UN SUB (UN PR q)))
  withObExp r = r
  curry (Prod (Sub (Prof n))) = Prod (Sub (Prof \p -> p // Exp \ca bd q -> n (dimap ca bd p :*: q)))
  apply = Prod (Sub (Prof \(Exp f :*: q) -> f id id q \\ q))
  Prod (Sub (Prof m)) ^^^ Prod (Sub (Prof n)) = Prod (Sub (Prof \(Exp f) -> Exp \ca bd p -> m (f ca bd (n p))))

instance (ThinProfunctor p, ThinProfunctor q, Discrete j, Discrete k) => ThinProfunctor (p :~>: q :: j +-> k) where
  type HasArrow (p :~>: q) a b = (HasArrow p a b :=> HasArrow q a b)
  arr @a @b = Exp \ca bd p -> withEq ca (withEq bd (withArr p (unEntails (entails @(HasArrow p a b) @(HasArrow q a b)) arr)))
  withArr @a @b (Exp f) r = reifyExp (Entails @(HasArrow p a b) @(HasArrow q a b) (\r' -> withArr (f id id arr) r')) r

-- | Implication, decided: the exponential holds unless @p@ holds and @q@ does not. Against @p@ an
-- arrow of @p@ is refuted by 'noArrow'.
instance
  (DecidableProfunctor p, DecidableProfunctor q, Discrete j, Discrete k)
  => DecidableProfunctor (p :~>: q :: j +-> k)
  where
  type Holds (p :~>: q) a b = BoolLeq (Holds p a b) (Holds q a b)
  decide @a @b = case (decide @p @a @b, decide @q @a @b) of
    (_, Yes y) -> Yes (Exp \ca bd _ -> withEq ca (withEq bd y))
    (No, No) -> Yes (Exp \ca bd x -> withEq ca (withEq bd (noArrow x)))
    (Yes _, No) -> No
  toHolds @a @b (Exp f) r = case decide @p @a @b of
    Yes x -> toHolds (f id id x) r
    No -> r
