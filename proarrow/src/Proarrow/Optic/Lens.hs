{-# LANGUAGE AllowAmbiguousTypes #-}

-- | The __lens__: the optic for the categorical product, with legs
--
-- > Lens s t a b = (s ~> a, (s && b) ~> t)
--
-- witnessed by @'Rep'@\/@'Corep'@ @('Product' s)@ ('LensFl' \/ 'putP'). The product residual is
-- the whole source @s@. A lens both views and sets, sitting below 'Proarrow.Optic.Getter.Getter'
-- and 'Proarrow.Optic.AffineTraversal.AffineTraversal' in the lattice. Build with 'lens' (or from
-- the van-Laarhoven form with 'lensVL'), eliminate to the two legs with 'withLens', via the
-- generic 'ExOptic' carrier.
module Proarrow.Optic.Lens where

import Data.Functor.Const (Const (..))
import Prelude (const, ($))
import Prelude qualified as P

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), Tensor)
import Proarrow.Category.Monoidal.Action (ActionAt)
import Proarrow.Category.Monoidal.Cartesian (Cartesian, TensorIsProduct, productToTensor, tensorToProduct)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, (\\), type (+->))
import Proarrow.Functor (Functor (map), Prelude (..))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), Product, first)
import Proarrow.Limit.BinaryProduct qualified as BP
import Proarrow.Object (pattern Objs)
import Proarrow.Optic
  ( ExOptic
  , FLAVOR
  , Optic
  , Optic_ (..)
  , Prostrong (..)
  , iso
  , legs2prof
  , withLegs
  )
import Proarrow.Optic.AffineTraversal (AffineTravFl (..))
import Proarrow.Optic.Getter (GetterFl (..))
import Proarrow.Optic.Glass (GlassFl)
import Proarrow.Optic.MonoidalLens ()
import Proarrow.Optic.TensorOps (Backward (..), Continuation (..), TensorRight (..))
import Proarrow.Optic.TensorOps qualified as OpticTensor
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Instance.Star (Star, unStar, pattern Star)
import Proarrow.Profunctor.Representable (Rep (..))

type LensFl :: forall {k}. FLAVOR k k
class (AffineTravFl p q, GetterFl p q, GlassFl p q) => LensFl (p :: k +-> k) (q :: k +-> k) where
  -- | Like 'affineSet', but with a weaker constraint. Lens witnesses only ever need binary
  -- products, so lenses stay usable in categories without coproducts.
  putP :: (HasBinaryProducts k) => p (s :: k) a -> q b t -> (s && b) ~> t
instance (HasBinaryProducts k, Ob (s :: k)) => LensFl (Rep (Product s)) (Corep (Product s)) where
  putP @_ @a @b (Rep p) (Corep q) = q . first @b (fst @k @s @a . p)
instance (CategoryOf k) => LensFl (Id :: k +-> k) (Id :: k +-> k) where
  putP @s @_ @b sa (Id bt) = bt . snd @k @s @b \\ sa \\ bt
instance (LensFl f g, LensFl f' g') => LensFl (f :.: f') (g' :.: g) where
  putP @s @_ @b (f@Objs :.: f') (g'@Objs :.: g) =
    putP @f @g f g . (fst @_ @s @b &&& (putP @f' @g' f' g' . first @b (getP @f @g f)))

type Lens (s :: k) (t :: k) a b = Optic (Prostrong LensFl) s t a b
type Lens' s a = Lens s s a a
lens
  :: forall {k} (s :: k) (t :: k) a b
   . (HasBinaryProducts k, Ob b) => (s ~> a) -> ((s && b) ~> t) -> Lens s t a b
lens sa sbt =
  legs2prof @LensFl (Rep @a @(Product s) (id &&& sa)) (Corep @b @(Product s) sbt) \\ sa

-- | Eliminate any optic that is at least an iso and at most a lens to its two legs, in either
-- encoding: run it at its witness pair ('ExOptic' 'LensFl', via 'withLegs') and read the legs off
-- with 'getP' and 'putP'.
withLens
  :: forall {k} c (s :: k) (t :: k) a b r
   . (HasBinaryProducts k, (Ob a, Ob b) => c (ExOptic LensFl a b))
  => Optic c s t a b -> ((s ~> a) -> ((s && b) ~> t) -> r) -> r
withLens o k = withLegs @LensFl o \ @p @q p q -> k (getP @p @q p) (putP @p @q p q)

instance (P.Functor f) => Prostrong LensFl (Star (Prelude f)) where
  proact @p @q (p@Objs :.: Star f :.: q@Objs) = Star \a -> map (P.curry (putP p q) a) (f (getP @p @q p a))

type LensVL s t a b = forall f. (P.Functor f) => (a -> f b) -> s -> f t
toLensVL :: Lens s t a b -> LensVL s t a b
toLensVL (Optic l) = (unPrelude .) . unStar . l . Star . (Prelude .)

lensVL :: LensVL s t a b -> Lens s t a b
lensVL f = lens (getConst . f Const) (P.uncurry (f (const id)))

-- Tensor witnesses are also product-lens witnesses when tensor is product.
instance (Cartesian k, Ob m) => LensFl (Rep (ActionAt Tensor m) :: k +-> k) (Corep (ActionAt Tensor m)) where
  putP @_ @a @b (Rep forward) (Corep backward) =
    backward . productToTensor @m @b . first @b (fst @k @m @a . tensorToProduct @m @a . forward)

-- Product/tensor adapters are confined to the boundaries of the update.
putTensorRight
  :: forall {k} (u :: k) v s t b
   . ( Monoidal k
     , HasBinaryProducts k
     , TensorIsProduct s u
     , TensorIsProduct b v
     , TensorIsProduct t v
     , Ob u
     , Ob v
     , Ob s
     , Ob t
     , Ob b
     )
  => (s && b ~> t) -> (s ** u) && (b ** v) ~> (t ** v)
putTensorRight put =
  withObProd @k @b @v $
    productToTensor @t @v
      . (put *** obj @v)
      . BP.associatorProdInv @s @b @v
      . (fst @k @s @u *** obj @(b && v))
      . (tensorToProduct @s @u *** tensorToProduct @b @v)

putBackward
  :: forall {k} (m :: k) s t b
   . (Monoidal k, HasBinaryProducts k, TensorIsProduct m b, TensorIsProduct m t, Ob m, Ob s, Ob t, Ob b)
  => (s && b ~> t) -> s && (m ** b) ~> (m ** t)
putBackward put =
  withOb2 @k @m @b $
    let carried = fst @k @m @b . tensorToProduct @m @b
        returned = snd @k @m @b . tensorToProduct @m @b
    in productToTensor @m @t
         . ((carried . snd @k @s @(m ** b)) &&& (put . (obj @s *** returned)))

instance (Cartesian k, Prostrong LensFl p, Ob u, Ob v) => Prostrong LensFl (TensorRight (p :: k +-> k) u v) where
  proact ((f@Objs :: f s a) :.: TensorRight p@Objs :.: (g@Objs :: g b t)) =
    withOb2 @k @s @u $
      withOb2 @k @t @v $
        TensorRight
          ( unOptic
              ( lens @(s ** u) @(t ** v) @(a ** u) @(b ** v)
                  (getP @f @g @s @a f ** obj @u)
                  (putTensorRight @u @v @s @t @b (putP @f @g @s @a @b f g))
              )
              p
          )

instance (Cartesian k, Prostrong LensFl p, Ob m) => Prostrong LensFl (Backward (p :: k +-> k) m) where
  proact ((f@Objs :: f s a) :.: Backward p@Objs :.: (g@Objs :: g b t)) =
    withOb2 @k @m @t $
      Backward
        ( unOptic
            ( lens @s @(m ** t) @a @(m ** b)
                (getP @f @g @s @a f)
                (putBackward @m @s @t @b (putP @f @g @s @a @b f g))
            )
            p
        )

instance
  ( Cartesian k
  , Ob s
  , Ob x
  , forall m p. (Ob m, output p, Profunctor p) => output (Backward p m)
  )
  => Prostrong LensFl (Continuation output (s :: k) x)
  where
  proact ((f@Objs :: f y z) :.: Continuation context :.: (g@Objs :: g t r)) =
    Continuation
      ( iso id (putP @f @g @y @z @t f g . tensorToProduct @y @t)
          . OpticTensor.strengthBackward @y context
          . iso id (productToTensor @y @z . (obj @y &&& getP @f @g @y @z f))
      )
