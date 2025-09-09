module Proarrow.Object.Terminal where

import Data.Kind (Type)
import Prelude (Eq, Show, type (~))

import Proarrow.Category.Instance.Free (Elem, FREE (..), Free (..), HasStructure (..), IsFreeOb (..), Ok, emb)
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), type (+->))
import Proarrow.Profunctor.Terminal (TerminalProfunctor (..))
import Proarrow.Tools.Laws (AssertEq (..), Laws (..), Var)

class (CategoryOf k, Ob (TerminalObject :: k)) => HasTerminalObject k where
  type TerminalObject :: k
  terminate :: (Ob (a :: k)) => a ~> TerminalObject

terminate' :: forall {k} a a'. (HasTerminalObject k) => (a :: k) ~> a' -> a ~> TerminalObject
terminate' a = terminate @k @a' . a \\ a

-- | The type of elements of `a`.
type El a = TerminalObject ~> a

instance HasTerminalObject Type where
  type TerminalObject = ()
  terminate _ = ()

instance (HasTerminalObject j, HasTerminalObject k) => HasTerminalObject (j, k) where
  type TerminalObject = '(TerminalObject, TerminalObject)
  terminate = terminate :**: terminate

instance (CategoryOf j, CategoryOf k) => HasTerminalObject (j +-> k) where
  type TerminalObject = TerminalProfunctor
  terminate = Prof \a -> TerminalProfunctor \\ a

class ((Unit :: k) ~ TerminalObject, HasTerminalObject k, Monoidal k) => Semicartesian k
instance ((Unit :: k) ~ TerminalObject, HasTerminalObject k, Monoidal k) => Semicartesian k

data family TermF :: k
instance (HasTerminalObject `Elem` cs) => IsFreeOb (TermF :: FREE cs p) where
  type Lower f TermF = TerminalObject
  withLowerOb r = r
instance (HasTerminalObject `Elem` cs) => HasStructure cs p HasTerminalObject where
  data Struct HasTerminalObject a b where
    Terminal :: (Ob a) => Struct HasTerminalObject a TermF
  foldStructure @f _ (Terminal @a) = withLowerOb @a @f (terminate)
deriving instance Eq (Struct HasTerminalObject a b)
deriving instance Show (Struct HasTerminalObject a b)
instance (Ok cs p, HasTerminalObject `Elem` cs) => HasTerminalObject (FREE cs p) where
  type TerminalObject = TermF
  terminate = Str Terminal Id

data instance Var '[HasTerminalObject] a b where
  F :: Var '[HasTerminalObject] "A" "B"
deriving instance Show (Var '[HasTerminalObject] a b)
instance Laws '[HasTerminalObject] where
  type EqTypes '[HasTerminalObject] = '[EMB "A", TermF]
  laws = [terminate . emb F :=: terminate]
