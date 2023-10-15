module Proarrow.Category.Bicategory where
import Data.Kind (Constraint, Type)
import Proarrow.Core (CategoryOf, Profunctor, PRO)
import Proarrow.Functor (Functor)

class Double sq where
  type Object sq k :: Constraint
  type Arrow sq (f :: j -> k) :: Constraint
  type Proarrow sq (p :: PRO j k) :: Constraint


  -- type O :: Kind i j -> Kind j k -> Kind i k
  -- type U o
  -- -- vcomp ::
  -- leftUnitor :: Ob a => U o `o` a ~> a
  -- leftUnitorInv :: Ob a => a ~> U o `o` a
  -- rightUnitor :: Ob a => a `o` U o ~> a
  -- rightUnitorInv :: Ob a => a ~> a `o` U o
  -- associator :: (a `o` b) `o` c ~> a `o` (b `o` c)
  -- associatorInv :: a `o` (b `o` c) ~> (a `o` b) `o` c

newtype ProfSq p q f g = ProfSq { getProfSq :: forall a b. p a b -> q (f a) (g b) }
instance Double ProfSq where
  type Object ProfSq k = CategoryOf k
  type Arrow ProfSq f = Functor f
  type Proarrow ProfSq p = Profunctor p