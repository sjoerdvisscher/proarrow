{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Carrier-based optic operations. Input and output constraints may differ:
-- an operation preserves a flavor when its carriers support that flavor, and
-- may weaken it when the operation introduces additional structure. No optic
-- is converted through its existential representation by these combinators.
--
-- Give the result a named optic type when choosing its flavor, for example:
--
-- @
-- paired :: Lens ((Bool, Bool), Bool) ((Bool, Bool), Bool) (Bool, Bool) (Bool, Bool)
-- paired = tensorOptic firstField negationIso
-- @
--
-- Here the first input is a lens and the second an iso, while the result stays
-- a lens. Their flavor modules supply the carrier instances; this module owns
-- only the operations and carriers. In particular it never chooses a flavor
-- at runtime or weakens an optic via 'Proarrow.Optic.convert'.
module Proarrow.Optic.TensorOps where

import Data.Kind (Constraint)
import Prelude (($))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..), Tensor)
import Proarrow.Category.Monoidal.Action (ActionAt)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, (\\), type (+->))
import Proarrow.Monoid (Comonoid (..))
import Proarrow.Object (pattern Objs)
import Proarrow.Optic (Optic, Optic_ (..), Prostrong, iso, legs2prof)
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Representable (Rep (..))

-- | Carry independent forward and backward wires alongside an optic.
firstOptic
  :: forall {k} (u :: k) v input output s t a b
   . ( Monoidal k
     , Ob u
     , Ob v
     , forall p. (output p, Profunctor p) => input (TensorRight p u v)
     )
  => Optic input s t a b -> Optic output (s ** u) (t ** v) (a ** u) (b ** v)
firstOptic o@Objs =
  withOb2 @k @s @u $
    withOb2 @k @t @v $
      withOb2 @k @a @u $
        withOb2 @k @b @v $
          Optic \(p :: p (a ** u) (b ** v)) ->
            case unOptic o (TensorRight @_ @u @v p) of TensorRight q -> q
{-# INLINE firstOptic #-}

data TensorRight (p :: k +-> k) (u :: k) v a b where
  TensorRight :: forall p u v a b. (Ob a, Ob b) => p (a ** u) (b ** v) -> TensorRight p u v a b

instance (Monoidal k, Profunctor p, Ob u, Ob v) => Profunctor (TensorRight (p :: k +-> k) u v) where
  dimap l r (TensorRight p) = TensorRight (dimap (l ** obj @u) (r ** obj @v) p) \\ l \\ r
  r \\ TensorRight{} = r

-- | Tensor optics, allowing the inputs to have different flavors.
tensorOptic
  :: forall {k} input1 input2 output (s :: k) t a b u v c d
   . ( SymMonoidal k
     , forall p. (output p, Profunctor p) => input1 (TensorRight p u v)
     , forall p. (output p, Profunctor p) => input2 (TensorRight p a b)
     )
  => Optic input1 s t a b
  -> Optic input2 u v c d
  -> Optic output (s ** u) (t ** v) (a ** c) (b ** d)
tensorOptic l@Objs r@Objs =
  firstOptic @u @v @input1 @output l
    . iso (swap @k @a @u) (swap @k @v @b)
    . firstOptic @a @b @input2 @output r
    . iso (swap @k @c @a) (swap @k @b @d)
{-# INLINE tensorOptic #-}

-- | Carry an extra value along just the backward wire.
strengthBackward
  :: forall {k} (m :: k) input output s t a b
   . ( Monoidal k
     , Ob m
     , forall p. (output p, Profunctor p) => input (Backward p m)
     )
  => Optic input s t a b -> Optic output s (m ** t) a (m ** b)
strengthBackward o@Objs =
  withOb2 @k @m @t $
    withOb2 @k @m @b $
      Optic \(p :: p a (m ** b)) ->
        case unOptic o (Backward @_ @m p) of Backward q -> q
{-# INLINE strengthBackward #-}

data Backward (p :: k +-> k) (m :: k) a b where
  Backward :: forall p m a b. (Ob a, Ob b) => p a (m ** b) -> Backward p m a b

instance (Monoidal k, Profunctor p, Ob m) => Profunctor (Backward (p :: k +-> k) m) where
  dimap l r (Backward p) = Backward (dimap l (obj @m ** r) p) \\ l \\ r
  r \\ Backward{} = r

-- | Plug an optic into the backward focus of another optic. The downstream
-- optic is interpreted directly at the continuation carrier of the output.
mapContinuation
  :: forall {k} input output (s :: k) x y r z t
   . (CategoryOf k, input (Continuation output s x))
  => Optic input y r z t -> Optic output s t x z -> Optic output s r x y
mapContinuation downstream@Objs context@Objs =
  case unOptic downstream (Continuation context) of Continuation result -> result
{-# INLINE mapContinuation #-}

data Continuation (output :: (k +-> k) -> Constraint) (s :: k) (x :: k) (a :: k) (b :: k) where
  Continuation :: (Ob a, Ob b) => Optic output s b x a -> Continuation output s x a b

instance (CategoryOf k, Ob s, Ob x) => Profunctor (Continuation output (s :: k) x) where
  dimap l r (Continuation context) = Continuation (iso id r . context . iso id l) \\ l \\ r
  r \\ Continuation{} = r

-- | Retain the sampled focus alongside the backward result. The output flavor
-- must admit the copying witness; an iso may therefore produce a lens here.
retainView
  :: forall {k} w input (s :: k) t a b
   . ( Comonoid a
     , w (Rep (ActionAt Tensor a)) (Corep (ActionAt Tensor a))
     , forall p. (Prostrong w p, Profunctor p) => input (Backward p a)
     )
  => Optic input s t a b -> Optic (Prostrong w) s (a ** t) a b
retainView o@Objs =
  withOb2 @k @a @b $
    strengthBackward @a @input @(Prostrong w) o
      . legs2prof @w (Rep @a @(ActionAt Tensor a) (comult @a)) (Corep @b @(ActionAt Tensor a) (obj @(a ** b)))
{-# INLINE retainView #-}
