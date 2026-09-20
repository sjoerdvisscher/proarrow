{-# LANGUAGE AllowAmbiguousTypes #-}

-- | The __glass__ (Clarke et al., /Profunctor optics: a categorical update/): the optic for the
-- combined action of the product and the exponential,
--
-- > Glass s t a b = exists c d. (s ~> c && (d ~~> a), (c && (d ~~> b)) ~> t)
--
-- which collapses to the single leg @(s && ((s ~~> a) ~~> b)) ~> t@: given the source and a way
-- to turn any /selector/ @s ~~> a@ into a @b@, produce a @t@. A lens is the case @d = Unit@ (it
-- applies the selector to the source it was given), a grate the case @c = Unit@ (it ignores the
-- source and feeds the selector through its exponent), so 'GlassFl' is the join of
-- 'Proarrow.Optic.Lens.LensFl' and 'Proarrow.Optic.Grate.GrateFl' -- what
-- 'Proarrow.Optic.AffineTraversal.AffineTravFl' is to lenses and prisms, one column over. Like
-- that flavor it has no witnesses of its own: its generating pairs are the product pair and the
-- exponential pair, and 'glass' packs its single leg as their composite.
--
-- It sits directly below 'Proarrow.Optic.Setter.SetterFl': a glass sets, but it neither folds
-- (grates do not) nor distributes an applicative (lenses do not).
module Proarrow.Optic.Glass where

import Prelude (($))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..), type (**))
import Proarrow.Category.Monoidal.Cartesian (CCC, productToTensor, tensorToProduct)
import Proarrow.Category.Monoidal.Closed (Closed (..), Exp, comp, mkExponential, swapClosed)
import Proarrow.Category.Monoidal.CopyDiscard (fst, snd, (&&&))
import Proarrow.Core (CategoryOf (..), Promonad (..), obj, type (+->))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (type (&&)), Product)
import Proarrow.Limit.BinaryProduct qualified as P
import Proarrow.Object (pattern Objs)
import Proarrow.Optic
  ( ExOptic
  , FLAVOR
  , Optic
  , Prostrong (..)
  , legs2prof
  , withLegs
  )
import Proarrow.Optic.Setter (SetterFl)
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (Rep (..))

-- | The glass flavor. Its one method is the collapsed leg; everything is stated in a cartesian
-- closed category, where the residual can be copied and selectors can be internalised.
type GlassFl :: forall {k}. FLAVOR k k
class (SetterFl p q) => GlassFl (p :: k +-> k) (q :: k +-> k) where
  glassP :: (CCC k) => p s a -> q b t -> (s && Mod s a b) ~> t

-- | A /modifier/: given a selector @s '~~>' a@ for reading the focus out of the source, it
-- produces the new focus @b@. It is the right half of a glass's single leg, and the whole of a
-- 'Proarrow.Optic.Grate.grate'\'s argument.
type Mod :: forall {k}. k -> k -> k -> k
type Mod s a b = (s ~~> a) ~~> b

-- | Feed a fixed selector @s ~> a@ to a 'Mod'.
applySel :: forall {k} (s :: k) a b. (Closed k, Ob s, Ob a, Ob b) => (s ~> a) -> Mod s a b ~> b
applySel sel =
  withObSel @s @a @b $
    apply @k @(s ~~> a) @b . (obj @(Mod s a b) ** mkExponential sel) . rightUnitorInv @k @(Mod s a b)

-- | The two 'Ob' facts every modifier needs: the selector type @s '~~>' a@ and the 'Mod' that
-- consumes it. Each 'GlassFl' instance below opens with this.
withObSel
  :: forall {k} (s :: k) a b r
   . (Closed k, Ob s, Ob a, Ob b) => ((Ob (s ~~> a), Ob (Mod s a b)) => r) -> r
withObSel r = withObExp @k @s @a (withObExp @k @(s ~~> a) @b r)

-- | The product pair, a lens witness: the selector is the lens's own @get@, applied to the source
-- at hand; the residual is kept.
instance (HasBinaryProducts k, Ob (c :: k)) => GlassFl (Rep (Product c)) (Corep (Product c)) where
  glassP @s @a @b (Rep h@Objs) (Corep i) =
    withObSel @s @a @b $
      i
        . tensorToProduct @c @b
        . ( (P.fst @k @c @a . h . fst @s @(Mod s a b))
              &&& (applySel @s @a @b (P.snd @k @c @a . h) . snd @s @(Mod s a b))
          )
        . productToTensor @s @(Mod s a b)

-- | The exponential pair, a grate witness: the source is ignored, and the consumer is fed the
-- selector @\\s -> h s d@ for each point @d@ of the exponent.
instance (Closed k, Ob (d :: k)) => GlassFl (Rep (Exp d)) (Corep (Exp d)) where
  glassP @s @a @b (Rep h@Objs) (Corep i) =
    withObSel @s @a @b $
      i
        . curry @k @(Mod s a b) @d (apply @k @(s ~~> a) @b . (obj @(Mod s a b) ** swapClosed @a @s @d h))
        . snd @s @(Mod s a b)
        . productToTensor @s @(Mod s a b)

instance (CategoryOf k) => GlassFl (Id :: k +-> k) (Id :: k +-> k) where
  glassP @s @a @b (Id l@Objs) (Id r@Objs) =
    withObSel @s @a @b $
      r . applySel @s @a @b l . snd @s @(Mod s a b) . productToTensor @s @(Mod s a b)

-- | Composition threads the selector through: the outer glass is given the consumer
-- @\\sel -> inner (sel s, \\sel' -> k (sel' . sel))@.
instance
  forall k (f :: k +-> k) (f' :: k +-> k) (g :: k +-> k) (g' :: k +-> k)
   . (GlassFl f g, GlassFl f' g')
  => GlassFl (f :.: f') (g' :.: g)
  where
  glassP @s @a @b (f@Objs :.: (f'@Objs :: f' x a)) ((g'@Objs :: g' b y) :.: g@Objs) =
    withObSel @s @a @b $
      withObSel @s @x @y $
        withObSel @x @a @b $
          withOb2 @k @s @(Mod s a b) $
            withOb2 @k @(s ** Mod s a b) @(s ~~> x) $
              withOb2 @k @((s ** Mod s a b) ** (s ~~> x)) @(x ~~> a) $
                let
                  -- the inner glass, fed a product-typed pair
                  inner = glassP @f' @g' f' g' . tensorToProduct @x @(Mod x a b)
                  -- the source of the inner glass: the outer selector applied to @s@
                  xpart =
                    apply @k @s @x
                      . ( snd @(s ** Mod s a b) @(s ~~> x)
                            &&& (fst @s @(Mod s a b) . fst @(s ** Mod s a b) @(s ~~> x))
                        )
                  -- the inner consumer: compose the selectors, hand the result to @k@
                  kk =
                    snd @s @(Mod s a b)
                      . fst @(s ** Mod s a b) @(s ~~> x)
                      . fst @((s ** Mod s a b) ** (s ~~> x)) @(x ~~> a)
                  sel =
                    comp @s @x @a
                      . ( snd @((s ** Mod s a b) ** (s ~~> x)) @(x ~~> a)
                            &&& (snd @(s ** Mod s a b) @(s ~~> x) . fst @((s ** Mod s a b) ** (s ~~> x)) @(x ~~> a))
                        )
                  kipart = curry @k @((s ** Mod s a b) ** (s ~~> x)) @(x ~~> a) (apply @k @(s ~~> a) @b . (kk &&& sel))
                  body = inner . (xpart &&& kipart)
                in
                  glassP @f @g f g
                    . tensorToProduct @s @(Mod s x y)
                    . (fst @s @(Mod s a b) &&& curry @k @(s ** Mod s a b) @(s ~~> x) body)
                    . productToTensor @s @(Mod s a b)

type Glass (s :: k) (t :: k) a b = Optic (Prostrong GlassFl) s t a b
type Glass' s a = Glass s s a a

-- | Build a glass from its single leg. The residuals are the whole source and the "logarithm"
-- @s ~~> a@, so the witness is the lens witness at @s@ composed with the grate witness at @s ~~> a@.
glass
  :: forall {k} (s :: k) (t :: k) a b
   . (CCC k, Ob s, Ob a, Ob b)
  => ((s && Mod s a b) ~> t) -> Glass s t a b
glass f =
  withObSel @s @a @a $
    withObExp @k @(s ~~> a) @b $
      let ev = curry @k @s @(s ~~> a) (apply @k @s @a . swap @k @s @(s ~~> a))
      in legs2prof @GlassFl
           (Rep @(Mod s a a) @(Product s) (id P.&&& ev) :.: Rep @a @(Exp (s ~~> a)) (obj @(Mod s a a)))
           (Corep @b @(Exp (s ~~> a)) (obj @(Mod s a b)) :.: Corep @(Mod s a b) @(Product s) f)

-- | Eliminate any glass-flavored optic (a lens, a grate, or a composite of both, in either
-- encoding) to its single leg.
withGlass
  :: forall {k} c (s :: k) (t :: k) a b r
   . (CCC k, (Ob a, Ob b) => c (ExOptic GlassFl a b))
  => Optic c s t a b -> (((s && Mod s a b) ~> t) -> r) -> r
withGlass o k = withLegs @GlassFl o \ @p @q p q -> k (glassP @p @q p q)
