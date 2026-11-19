{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Cartesian monoidal categories ('Cartesian': coherent tensor/product isomorphisms, with 'CopyDiscard' as
-- superclass by Fox's theorem), cartesian closed ones ('CCC') and bicartesian closed ones
-- ('BiCCC', which implies 'Distributive'): the meeting point of the monoidal and the product
-- worlds, which never import each other. Lives above
-- "Proarrow.Category.Monoidal.CopyDiscard" rather than with the products, because the superclass
-- points that way.
module Proarrow.Category.Monoidal.Cartesian
  ( Cartesian (..)
  , TensorIsProduct
  , CCC
  , BiCCC
  , Bicartesian
  , curryProd
  , applyProd
  , distLProd
  , distRProd
  , ap
  , unparRepCartesian
  , Struct (ProdToTensor, TensorToProd, TermToUnit, UnitToTerm)
  , prodToTensor
  , tensorToProd
  , termToUnit
  , unitToTerm
  ) where

import Data.Kind (Constraint, Type)
import Prelude (($), type (~))
import Prelude qualified as P

import Proarrow.Category.Instance.Bool (BOOL)
import Proarrow.Category.Instance.Free
  ( Elems
  , FREE
  , Free (..)
  , HasStructure (..)
  , Lower
  , withLowerOb
  )
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Sub (IsObProd, SUBCAT (..), Sub (..), SubMonoidal)
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal, type (**!))
import Proarrow.Category.Monoidal.Closed (Closed (..), uncurry)
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard (..))
import Proarrow.Category.Monoidal.Distributive (Distributive (..), Traversable (..))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..), type (||))
import Proarrow.Core (CAT, CategoryOf (..), Kind, OB, Profunctor (..), Promonad (..), UN, lmap, type (+->))
import Proarrow.Limit.BinaryProduct
  ( HasBinaryProducts (..)
  , HasProducts
  , PROD (..)
  , Prod (..)
  , diag
  , swapProd
  , type (*!)
  )
import Proarrow.Limit.Terminal (HasTerminalObject (..), Semicartesian (..), Struct (TermToUnit, UnitToTerm))
import Proarrow.Limit.Terminal qualified as Terminal
import Proarrow.Monoid (CocommutativeComonoid, Comonoid (..), Supplies)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Product ((:*:) (..))
import Proarrow.Profunctor.Representable (RepCostar (..), Representable (..), withObRep)

type TensorIsProduct :: forall {k}. k -> k -> Constraint
class (a ** b ~ a && b) => TensorIsProduct a b
instance (a ** b ~ a && b) => TensorIsProduct a b

-- | A cartesian monoidal category: the tensor coherently presents the categorical
-- product. The supplied copy/discard maps are the natural diagonals and terminal
-- maps, transported along these mutually inverse, natural isomorphisms and
-- those of 'Semicartesian'. Strict instances use identity defaults.
type Cartesian :: Kind -> Constraint
class (HasProducts k, Semicartesian k, CopyDiscard k) => Cartesian k where
  productToTensor :: forall (a :: k) b. (Ob a, Ob b) => (a && b) ~> (a ** b)
  default productToTensor :: forall (a :: k) b. (Ob a, Ob b, TensorIsProduct a b) => (a && b) ~> (a ** b)
  productToTensor = withObProd @k @a @b id

  tensorToProduct :: forall (a :: k) b. (Ob a, Ob b) => (a ** b) ~> (a && b)
  default tensorToProduct :: forall (a :: k) b. (Ob a, Ob b, TensorIsProduct a b) => (a ** b) ~> (a && b)
  tensorToProduct = withObProd @k @a @b id

instance Cartesian Type
instance Cartesian ()
instance Cartesian BOOL where
  productToTensor @a @b = withObProd @BOOL @a @b id
  tensorToProduct @a @b = withObProd @BOOL @a @b id
instance (HasProducts k) => Cartesian (PROD k) where
  productToTensor @a @b = withObProd @(PROD k) @a @b id
  tensorToProduct @a @b = withObProd @(PROD k) @a @b id
instance (Cartesian j, Cartesian k) => Cartesian (j, k) where
  productToTensor @'(a, a') @'(b, b') = productToTensor @j @a @b :**: productToTensor @k @a' @b'
  tensorToProduct @'(a, a') @'(b, b') = tensorToProduct @j @a @b :**: tensorToProduct @k @a' @b'

-- | In a category with products every object is a comonoid via the diagonal and the terminal
-- map. With this comonoid structure 'PROD' is 'CopyDiscard' and 'Cartesian'.
instance (HasProducts k, Ob a) => Comonoid (PR (a :: k)) where
  counit = Prod terminate
  comult = Prod diag

instance (HasProducts k, Ob a) => CocommutativeComonoid (PR (a :: k))

-- | A category with products, viewed through 'PROD' as a monoidal category, is cartesian.
instance (HasProducts k) => CopyDiscard (PROD k)

instance Closed (PROD Type) where
  -- The wrapper must also stay opaque until the helper's inlining phase.
  {-# INLINE [0] curry #-}
  type a ~~> b = PR (UN PR a ~~> UN PR b)
  withObExp @(PR a) @(PR b) r = withObExp @Type @a @b r
  curry (Prod f) = Prod (curryProd f)
  apply @(PR a) @(PR b) = Prod (applyProd @a @b)

-- | Every functor between cartesian categories is oplax monoidal, @f (a && b) ~> f a && f b@ by the
-- projections and @f Unit ~> Unit@ by terminality. On the 'RepCostar' of its representable profunctor
-- this is 'Proarrow.Category.Monoidal.OplaxMonoidal'.
instance (Representable p, Cartesian j, Cartesian k) => MonoidalProfunctor (RepCostar (p :: j +-> k)) where
  one = withObRep @p @Unit (RepCostar (Terminal.termToUnit . terminate))
  RepCostar @a f ** RepCostar @b g = withOb2 @j @a @b (RepCostar (unparRepCartesian @p @a @b f g))

unparRepCartesian
  :: forall {j} {k} p (a :: j) b a' b'
   . ( Representable (p :: j +-> k)
     , Cartesian k
     , Cartesian j
     , Ob a
     , Ob b
     )
  => (p % a ~> a') -> (p % b ~> b') -> p % (a ** b) ~> (a' ** b')
unparRepCartesian f g =
  productToTensor @_ @a' @b'
    . ( (f . repMap @p (fst @j @a @b . tensorToProduct @_ @a @b))
          &&& (g . repMap @p (snd @j @a @b . tensorToProduct @_ @a @b))
      )
    \\ f
    \\ g

class (Cartesian k, Closed k) => CCC k
instance (Cartesian k, Closed k) => CCC k

-- | Currying with the product, obtained from 'curry' using 'tensorToProduct'.
-- It satisfies the currying bijection in the laws of 'Closed'.
-- Keep @INLINE [0]@ on a delegating instance method too, to preserve delayed inlining.
curryProd :: forall {k} (a :: k) b c. (CCC k, Ob a, Ob b) => (a && b) ~> c -> a ~> (b ~~> c)
curryProd f = curry @k @a @b (f . tensorToProduct @_ @a @b)
-- Delay exposing the underlying curry to limit dictionary expansion in nested SMC terms.
{-# INLINE [0] curryProd #-}

-- | Evaluation with the product, obtained from 'apply' using 'productToTensor'.
-- Together with 'curryProd' it satisfies the currying bijection in the laws of 'Closed'.
applyProd :: forall {k} (a :: k) b. (CCC k, Ob a, Ob b) => ((a ~~> b) && a) ~> b
applyProd = withObExp @k @a @b (apply @k @a @b . productToTensor @_ @(a ~~> b) @a)
{-# INLINE applyProd #-}

type Bicartesian k = (Cartesian k, Distributive k)

-- | Bicartesian closed: cartesian closed with coproducts. Every such category is distributive
-- (@a &&@ is a left adjoint, so it preserves coproducts), and the class says so, so that
-- 'Distributive' never has to be asked for separately.
class (CCC k, Distributive k) => BiCCC k

instance (CCC k, Distributive k) => BiCCC k

-- | Distributivity of the /product/ over coproducts, derived from closedness: in any BiCCC the
-- functor @a &&@ is a left adjoint and so preserves coproducts.
distLProd :: forall {k} (a :: k) (b :: k) (c :: k). (BiCCC k, Ob a, Ob b, Ob c) => (a && (b || c)) ~> (a && b || a && c)
distLProd = (swapProd @b @a +++ swapProd @c @a) . distRProd @b @c @a . withObCoprod @k @b @c (swapProd @a @(b || c))

distRProd :: forall {k} (a :: k) (b :: k) (c :: k). (BiCCC k, Ob a, Ob b, Ob c) => ((a || b) && c) ~> (a && c || b && c)
distRProd =
  withObCoprod @k @a @b $
    withObProd @k @a @c $
      withObProd @k @b @c $
        withObCoprod @k @(a && c) @(b && c) $
          uncurry @c (curryProd @a @c (lft @k @(a && c) @(b && c)) ||| curryProd @b @c (rgt @k @(a && c) @(b && c)))
            . productToTensor @_ @(a || b) @c

instance (BiCCC k) => Distributive (PROD k) where
  distL @(PR a) @(PR b) @(PR c) = Prod (distLProd @a @b @c)
  distR @(PR a) @(PR b) @(PR c) = Prod (distRProd @a @b @c)
  absorbL @(PR a) = Prod (snd @k @a)
  absorbR @(PR a) = Prod (fst @k @_ @a)

instance (Cartesian k, Traversable p, Traversable q) => Traversable ((p :: k +-> k) :*: q) where
  traverse ((p :*: q) :.: r) = case (traverse (p :.: r), traverse (q :.: r)) of
    ((:.:) @a r' p', (:.:) @b r'' q') ->
      lmap copy (r' ** r'')
        :.: (lmap (fst @k @a @b . tensorToProduct @k @a @b) p' :*: lmap (snd @k @a @b . tensorToProduct @k @a @b) q')
        \\ p
        \\ p'
        \\ q'

ap
  :: forall {j} {k} y a x p
   . (Closed j, Cartesian k, MonoidalProfunctor (p :: j +-> k), Ob y)
  => p a (x ~~> y)
  -> p a x
  -> p a y
ap pf px = dimap copy (apply @j @x @y) (pf ** px) \\ px

-- | Formal tensor/product coherence maps for the free category.
instance
  ('[Cartesian, HasTerminalObject, HasBinaryProducts, Monoidal] `Elems` cs)
  => HasStructure cs (p :: CAT k) Cartesian
  where
  data Struct Cartesian i o where
    ProdToTensor :: (Ob a, Ob b) => Struct Cartesian (a *! b) (a **! b)
    TensorToProd :: (Ob a, Ob b) => Struct Cartesian (a **! b) (a *! b)
  sameStructure ProdToTensor ProdToTensor = P.True
  sameStructure TensorToProd TensorToProd = P.True
  sameStructure _ _ = P.False
  foldStructure @f _ (ProdToTensor @a @b) = P.pure P.$ withLowerOb @f @a (withLowerOb @f @b (productToTensor @_ @(Lower f a) @(Lower f b)))
  foldStructure @f _ (TensorToProd @a @b) = P.pure P.$ withLowerOb @f @a (withLowerOb @f @b (tensorToProduct @_ @(Lower f a) @(Lower f b)))

instance P.Show (Struct Cartesian a b) where
  showsPrec _ ProdToTensor = P.showString "prodToTensor"
  showsPrec _ TensorToProd = P.showString "tensorToProd"

-- | The formal @tensor = product@ isomorphisms of a free category with 'Cartesian' in its list.
prodToTensor
  :: forall {k} {cs} {p :: CAT k} (a :: FREE cs p) b
   . ('[Cartesian, HasTerminalObject, HasBinaryProducts, Monoidal] `Elems` cs, Ob a, Ob b)
  => (a *! b) ~> (a **! b)
prodToTensor = St ProdToTensor Nil

tensorToProd
  :: forall {k} {cs} {p :: CAT k} (a :: FREE cs p) b
   . ('[Cartesian, HasTerminalObject, HasBinaryProducts, Monoidal] `Elems` cs, Ob a, Ob b)
  => (a **! b) ~> (a *! b)
tensorToProd = St TensorToProd Nil

instance
  ( '[Cartesian, HasTerminalObject, HasBinaryProducts, Monoidal, SymMonoidal, Terminal.Semicartesian, Supplies Comonoid]
      `Elems` cs
  )
  => Cartesian (FREE cs (p :: CAT k))
  where
  productToTensor @a @b = prodToTensor @a @b
  tensorToProduct @a @b = tensorToProd @a @b

instance
  (Cartesian k, SubMonoidal ob, ob (TerminalObject :: k), forall a b. (ob a, ob b) => IsObProd ob a b)
  => Cartesian (SUBCAT (ob :: OB k))
  where
  productToTensor @(SUB a) @(SUB b) = Sub (productToTensor @k @a @b)
  tensorToProduct @(SUB a) @(SUB b) = Sub (tensorToProduct @k @a @b)
