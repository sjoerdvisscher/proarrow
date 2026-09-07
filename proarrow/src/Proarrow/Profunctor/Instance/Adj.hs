{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The 'Adj' newtype marks a profunctor as the heteromorphism profunctor of an adjunction: because left
-- adjoints preserve colimits and right adjoints preserve limits, @Adj p@ is a distributive monoidal
-- profunctor. Also proves that every adjunction between Hask endofunctors is equivalent to the
-- curry\/uncurry adjunction ('haskAdjIsCurryAdj').
module Proarrow.Profunctor.Instance.Adj where

import Data.Kind (Type)
import Prelude (const)

import Proarrow.Adjunction (Adjunction)
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Colimit.BinaryCoproduct (Coprod (..), HasBinaryCoproducts (..), HasCoproducts)
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (Profunctor (..), Promonad (..), lmap, rmap, type (+->))
import Proarrow.Limit.BinaryProduct (Cartesian, HasBinaryProducts (..))
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Object (pattern Objs)
import Proarrow.Optic (PIso, iso)
import Proarrow.Optic.Getter (review, view)
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), corepObj)
import Proarrow.Profunctor.Representable (Representable (..), repObj)

-- | Preservation of limits and colimits makes the adjunction heteromorphism a distributive profunctor.
newtype Adj p a b = Adj (p a b)
  deriving newtype (Profunctor, Representable, Corepresentable)

instance (Cartesian j, Cartesian k, Corepresentable p) => MonoidalProfunctor (Adj p :: j +-> k) where
  one = cotabulate terminate \\ corepObj @p @TerminalObject
  Adj @_ @x l@Objs ** Adj @_ @y r@Objs =
    withOb2 @_ @x @y
      ( cotabulate
          ( coindex @p @(x ** y) (lmap (fst @_ @x @y) l)
              &&& coindex @p @(x ** y) (lmap (snd @_ @x @y) r)
          )
      )

instance (HasCoproducts j, HasCoproducts k, Representable p) => MonoidalProfunctor (Coprod (Adj p :: j +-> k)) where
  one = tabulate initiate \\ repObj @p @InitialObject
  Coprod (Adj @_ @_ @x l@Objs) ** Coprod (Adj @_ @_ @y r@Objs) =
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

-- | Every adjunction between Hask endofunctors is equivalent to the curry-uncurry adjunction.
haskAdjIsCurryAdj
  :: forall p a b a' b'
   . (Adjunction (p :: Type +-> Type)) => PIso (p %% () -> a -> b) (p %% () -> a' -> b') (p a b) (p a' b')
haskAdjIsCurryAdj =
  iso (\kab -> tabulate \a -> index @p (cotabulate (`kab` a)) ()) (\p k a -> coindex p (corepMap @p (\() -> a) k))

instance (Adjunction p) => Promonad (Adj p :: Type +-> Type) where
  id = Adj (view (haskAdjIsCurryAdj @p) (const id))
  Adj l . Adj r = Adj (view (haskAdjIsCurryAdj @p) (\k -> review haskAdjIsCurryAdj l k . review haskAdjIsCurryAdj r k))
