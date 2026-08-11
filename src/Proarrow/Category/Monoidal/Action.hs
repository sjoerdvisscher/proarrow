{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Monoidal.Action where

import Data.Kind (Constraint)

import Proarrow.Category.Instance.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), Tensor)
import Proarrow.Colimit.BinaryCoproduct
  ( COPROD (..)
  , Coprod (..)
  , HasBinaryCoproducts (..)
  , HasCoproducts
  , associatorCoprod
  , associatorCoprodInv
  , leftUnitorCoprod
  , leftUnitorCoprodInv
  )
import Proarrow.Core (CategoryOf (..), OB, Promonad (..), obj, type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Limit.BinaryProduct
  ( HasBinaryProducts (..)
  , HasProducts
  , PROD (..)
  , Prod (..)
  , associatorProd
  , associatorProdInv
  , leftUnitorProd
  , leftUnitorProdInv
  )
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (Rep (..), Representable (..))

type Act :: (m, k) +-> k -> m -> k -> k
type Act t a x = t % '(a, x)

type MonoidalAction :: forall {m} {k}. (m, k) +-> k -> Constraint
class (Representable t, Monoidal m) => MonoidalAction (t :: (m, k) +-> k) where
  unitor :: (Ob x) => Act t Unit x ~> x
  unitorInv :: (Ob x) => x ~> Act t Unit x
  multiplicator :: (Ob a, Ob b, Ob x) => Act t (a ** b) x ~> Act t a (Act t b x)
  multiplicatorInv :: (Ob a, Ob b, Ob x) => Act t a (Act t b x) ~> Act t (a ** b) x

actHom :: (Representable t) => a ~> b -> x ~> y -> Act t a x ~> Act t b y
actHom @t l r = repMap @t (l :**: r)

composeActs
  :: forall {m} {k} t (x :: m) (y :: m) (c :: k) (a :: k) (b :: k)
   . (MonoidalAction t, Ob x, Ob y, Ob c)
  => a ~> Act t x b
  -> b ~> Act t y c
  -> a ~> Act t (x ** y) c
composeActs f g = multiplicatorInv @t @x @y @c . actHom @t (obj @x) g . f

decomposeActs
  :: forall {m} {k} t (x :: m) (y :: m) (c :: k) (a :: k) (b :: k)
   . (MonoidalAction t, Ob x, Ob y, Ob c)
  => Act t y c ~> b
  -> Act t x b ~> a
  -> Act t (x ** y) c ~> a
decomposeActs f g = g . actHom @t (obj @x) f . multiplicator @t @x @y @c

data family NoAction :: ((), k) +-> k
instance (CategoryOf k) => FunctorForRep (NoAction :: ((), k) +-> k) where
  type NoAction @ '(a, x) = x
  fmap (U.Unit :**: f) = f
instance (CategoryOf k) => MonoidalAction (Rep NoAction :: ((), k) +-> k) where
  unitor = id
  unitorInv = id
  multiplicator = id
  multiplicatorInv = id

data family OpAction :: (m, k) +-> k -> (OPPOSITE m, OPPOSITE k) +-> OPPOSITE k
instance (Representable (t :: (m, k) +-> k), CategoryOf m) => FunctorForRep (OpAction t) where
  type OpAction t @ '(OP a, OP x) = OP (t % '(a, x))
  fmap (Op l :**: Op r) = Op (actHom @t l r)
instance (MonoidalAction t) => MonoidalAction (Rep (OpAction t)) where
  unitor = Op (unitorInv @t)
  unitorInv = Op (unitor @t)
  multiplicator @(OP a) @(OP b) @(OP x) = Op (multiplicatorInv @t @a @b @x)
  multiplicatorInv @(OP a) @(OP b) @(OP x) = Op (multiplicator @t @a @b @x)

type SubAction ob t = Rep (SubAction' ob t)
data family SubAction' :: forall (ob :: OB m) -> (m, k) +-> k -> (SUBCAT ob, k) +-> k
instance (Monoidal k, Monoidal (SUBCAT (ob :: OB k)), Representable t) => FunctorForRep (SubAction' ob t) where
  type SubAction' ob t @ '(SUB a, x) = t % '(a, x)
  fmap (Sub f :**: g) = repMap @t (f :**: g)
instance (Monoidal k, Monoidal (SUBCAT (ob :: OB k)), MonoidalAction t) => MonoidalAction (SubAction ob t) where
  unitor = unitor @t
  unitorInv = unitorInv @t
  multiplicator @(SUB p) @(SUB q) @x = multiplicator @t @p @q @x
  multiplicatorInv @(SUB p) @(SUB q) @x = multiplicatorInv @t @p @q @x

instance (Monoidal k) => MonoidalAction (Tensor :: (k, k) +-> k) where
  unitor = leftUnitor @k
  unitorInv = leftUnitorInv @k
  multiplicator @a @b @x = associator @k @a @b @x
  multiplicatorInv @a @b @x = associatorInv @k @a @b @x

type ProdAction = Rep ProdAction'
data family ProdAction' :: (PROD k, k) +-> k
instance (HasProducts k) => FunctorForRep (ProdAction' :: (PROD k, k) +-> k) where
  type ProdAction' @ '(PR a, b) = a && b
  fmap (Prod p :**: q) = p *** q
instance (HasProducts k) => MonoidalAction (ProdAction :: (PROD k, k) +-> k) where
  unitor = leftUnitorProd
  unitorInv = leftUnitorProdInv
  multiplicator @(PR a) @(PR b) @x = associatorProd @a @b @x
  multiplicatorInv @(PR a) @(PR b) @x = associatorProdInv @a @b @x

type CoprodAction = Rep CoprodAction'
data family CoprodAction' :: (COPROD k, k) +-> k
instance (HasCoproducts k) => FunctorForRep (CoprodAction' :: (COPROD k, k) +-> k) where
  type CoprodAction' @ '(COPR a, x) = a || x
  fmap (Coprod (Id l) :**: r) = l +++ r
instance (HasCoproducts k) => MonoidalAction (CoprodAction :: (COPROD k, k) +-> k) where
  unitor = leftUnitorCoprod
  unitorInv = leftUnitorCoprodInv
  multiplicator @(COPR a) @(COPR b) @x = associatorCoprod @a @b @x
  multiplicatorInv @(COPR a) @(COPR b) @x = associatorCoprodInv @a @b @x

-- newtype Action a x y = Action (Rep (Action' a) x y)
-- deriving newtype instance (Ob (a :: m), MonoidalAction m k) => Profunctor (Action a :: k +-> k)
-- deriving newtype instance (Ob (a :: m), MonoidalAction m k) => Representable (Action a :: k +-> k)

-- data family Action' :: m -> k +-> k
-- instance (MonoidalAction m k, Ob a) => FunctorForRep (Action' (a :: m) :: k +-> k) where
--   type Action' a @ x = Act a x
--   fmap = act @m (obj @a)

-- par0Action :: (MonoidalAction m k, Ob (x :: k)) => Action (Unit :: m) x x
-- par0Action @m @k = Action (Rep (unitorInv @m @k))

-- parAction
--   :: forall {m} {k} a b x y z
--    . (MonoidalAction m k, Ob a, Ob b) => Action (a :: m) (x :: k) y -> Action (b :: m) y z -> Action (a ** b) x z
-- parAction (Action (Rep f)) (Action (Rep g)) = Action (Rep (composeActs @a @b @z f g))
