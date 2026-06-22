{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Instance.Duploid where

import Data.Kind (Constraint)
import Prelude (($))

import Proarrow.Adjunction (AdjMonad, Adjunction)
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), StrongMonoidalCorep, SymMonoidal (..))
import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Kind
  , Profunctor (..)
  , Promonad (..)
  , dimapDefault
  , lmap
  , obj
  , rmap
  , (//)
  , type (+->)
  )
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), trivialCorep, withObCorep)
import Proarrow.Profunctor.Representable (CorepStar (..), Representable (..), trivialRep, withObRep)

type DUPLOID :: forall {n} {p}. n +-> p -> Kind
type data DUPLOID (adj :: n +-> p) = N n | P p

data SDuploidObj x where
  SN :: (Ob x) => SDuploidObj (N x)
  SP :: (Ob x) => SDuploidObj (P x)

type IsPN :: forall {n} {p} {adj}. DUPLOID (adj :: n +-> p) -> Constraint
class IsPN x where
  pn :: SDuploidObj x
  withPosOb :: ((Ob (Pos x)) => r) -> r
  withNegOb :: ((Ob (Neg x)) => r) -> r
instance (Ob x, Corepresentable adj) => IsPN (P x :: DUPLOID adj) where
  pn = SP
  withPosOb r = r
  withNegOb r = withObCorep @adj @x r
instance (Ob x, Representable adj) => IsPN (N x :: DUPLOID adj) where
  pn = SN
  withPosOb r = withObRep @adj @x r
  withNegOb r = r

type family Pos (x :: DUPLOID (adj :: n +-> p)) :: p where
  Pos (P a) = a
  Pos (N a :: DUPLOID adj) = adj % a

type family Neg (x :: DUPLOID (adj :: n +-> p)) :: n where
  Neg (P a :: DUPLOID adj) = adj %% a
  Neg (N a) = a

type Duploid :: CAT (DUPLOID adj)
data Duploid x y where
  Duploid :: forall {adj} (x :: DUPLOID adj) y. (Ob x, Ob y) => adj (Pos x) (Neg y) -> Duploid x y

instance (Adjunction adj) => Profunctor (Duploid :: CAT (DUPLOID adj)) where
  dimap = dimapDefault
  r \\ Duploid{} = r

-- | ATTENTION: a duploid is not associative, so not really a promonad/category!
instance (Adjunction adj) => Promonad (Duploid :: CAT (DUPLOID adj)) where
  id @x = Duploid $ case pn @x of
    SP -> trivialCorep
    SN -> trivialRep
  g@(Duploid @y _) . f = case pn @y of
    SP -> g • f
    SN -> g ◦ f

instance (Adjunction adj) => CategoryOf (DUPLOID adj) where
  type (~>) = Duploid
  type Ob x = IsPN x

(•) :: forall {adj} (x :: DUPLOID adj) y z. (Corepresentable adj) => P y ~> z -> x ~> P y -> x ~> z
Duploid g • Duploid f = Duploid (rmap (coindex g) f)

(◦) :: forall {adj} (x :: DUPLOID adj) y z. (Representable adj) => N y ~> z -> x ~> N y -> x ~> z
Duploid g ◦ Duploid f = Duploid (lmap (index f) g)

fromThunkable :: forall {adj} (x :: DUPLOID adj) y. (Adjunction adj, Ob x, Ob y) => Pos x ~> Pos y -> x ~> y
fromThunkable f = Duploid (case pn @y of SN -> tabulate f; SP -> cotabulate (corepMap @adj f)) \\ f

fromLinear :: forall {adj} (x :: DUPLOID adj) y. (Adjunction adj, Ob x, Ob y) => Neg x ~> Neg y -> x ~> y
fromLinear f = Duploid (case pn @x of SN -> tabulate (repMap @adj f); SP -> cotabulate f) \\ f

type Dn x = P (Pos x)

down :: forall {adj} (x :: DUPLOID adj). (Adjunction adj, Ob x) => x ~> Dn x
down = withPosOb @x $ Duploid trivialCorep

undown :: forall {adj} (x :: DUPLOID adj). (Adjunction adj, Ob x) => Dn x ~> x
undown = withPosOb @x $ fromThunkable (obj @(Pos x))

mapDown :: forall {adj} (x :: DUPLOID adj) y. (Adjunction adj) => x ~> y -> Dn x ~> (Dn y :: DUPLOID adj)
mapDown f = down . f . undown \\ f

type Up x = N (Neg x)

unup :: forall {adj} (x :: DUPLOID adj). (Adjunction adj, Ob x) => Up x ~> x
unup = withNegOb @x $ Duploid trivialRep

up :: forall {adj} (x :: DUPLOID adj). (Adjunction adj, Ob x) => x ~> Up x
up = withNegOb @x $ fromLinear (obj @(Neg x))

mapUp :: forall {adj} (x :: DUPLOID adj) y. (Adjunction adj) => x ~> y -> Up x ~> (Up y :: DUPLOID adj)
mapUp f = up . f . unup \\ f

instance (Adjunction (adj :: n +-> p), StrongMonoidalCorep adj) => MonoidalProfunctor (Duploid :: CAT (DUPLOID adj)) where
  par0 = id
  par @_ @x2 @_ @y2 f g =
    f // g // case (down . f, down . g) of
      (Duploid fp, Duploid gp) ->
        withPosOb @x2 $
          withPosOb @y2 $
            withOb2 @_ @(Pos x2) @(Pos y2) $
              withObCorep @adj @(Pos x2 ** Pos y2) $
                case lmap (index fp) (trivialRep @(AdjMonad adj) @(Pos x2))
                  `par` lmap (index gp) (trivialRep @(AdjMonad adj) @(Pos y2)) of
                  fg :.: CorepStar h -> Duploid (rmap h fg) \\ fg

instance (Adjunction (adj :: n +-> p), StrongMonoidalCorep adj) => Monoidal (DUPLOID adj) where
  type x ** y = P (Pos x ** Pos y)
  type Unit = P Unit
  withOb2 @a @b r = withPosOb @a $ withPosOb @b $ withOb2 @_ @(Pos a) @(Pos b) r
  leftUnitor @a = withPosOb @a $ withOb2 @_ @Unit @(Pos a) $ fromThunkable (leftUnitor @_ @(Pos a))
  leftUnitorInv @a = withPosOb @a $ withOb2 @_ @Unit @(Pos a) $ fromThunkable (leftUnitorInv @_ @(Pos a))
  rightUnitor @a = withPosOb @a $ withOb2 @_ @(Pos a) @Unit $ fromThunkable (rightUnitor @_ @(Pos a))
  rightUnitorInv @a = withPosOb @a $ withOb2 @_ @(Pos a) @Unit $ fromThunkable (rightUnitorInv @_ @(Pos a))
  associator @a @b @c =
    withPosOb @a $
      withPosOb @b $
        withPosOb @c $
          withOb2 @_ @(Pos a) @(Pos b) $
            withOb2 @_ @(Pos a ** Pos b) @(Pos c) $
              withOb2 @_ @(Pos b) @(Pos c) $
                withOb2 @_ @(Pos a) @(Pos b ** Pos c) $
                  fromThunkable (associator @_ @(Pos a) @(Pos b) @(Pos c))
  associatorInv @a @b @c =
    withPosOb @a $
      withPosOb @b $
        withPosOb @c $
          withOb2 @_ @(Pos a) @(Pos b) $
            withOb2 @_ @(Pos a ** Pos b) @(Pos c) $
              withOb2 @_ @(Pos b) @(Pos c) $
                withOb2 @_ @(Pos a) @(Pos b ** Pos c) $
                  fromThunkable (associatorInv @_ @(Pos a) @(Pos b) @(Pos c))

type StrongSymMonAdj (adj :: n +-> p) = (Adjunction adj, StrongMonoidalCorep adj, SymMonoidal p)

instance (StrongSymMonAdj adj) => SymMonoidal (DUPLOID adj) where
  swap @a @b =
    withPosOb @a $
      withPosOb @b $
        withOb2 @_ @(Pos a) @(Pos b) $
          withOb2 @_ @(Pos b) @(Pos a) $
            fromThunkable (swap @_ @(Pos a) @(Pos b))

instance (HasBinaryCoproducts p, Adjunction adj) => HasBinaryCoproducts (DUPLOID (adj :: n +-> p)) where
  type a || b = P (Pos a || Pos b)
  withObCoprod @a @b r = withPosOb @a $ withPosOb @b $ withObCoprod @p @(Pos a) @(Pos b) r
  lft @a @b = withPosOb @a $ withPosOb @b $ withObCoprod @p @(Pos a) @(Pos b) $ fromThunkable (lft @p @(Pos a) @(Pos b))
  rgt @a @b = withPosOb @a $ withPosOb @b $ withObCoprod @p @(Pos a) @(Pos b) $ fromThunkable (rgt @p @(Pos a) @(Pos b))
  Duploid @x @a f ||| Duploid @y g =
    withPosOb @x $
      withPosOb @y $
        withObCoprod @p @(Pos x) @(Pos y) $
          withNegOb @a $
            Duploid $
              tabulate (index f ||| index g)

instance (HasBinaryProducts n, Adjunction adj) => HasBinaryProducts (DUPLOID (adj :: n +-> p)) where
  type a && b = N (Neg a && Neg b)
  withObProd @a @b r = withNegOb @a $ withNegOb @b $ withObProd @n @(Neg a) @(Neg b) r
  fst @a @b = withNegOb @a $ withNegOb @b $ withObProd @n @(Neg a) @(Neg b) $ fromLinear (fst @n @(Neg a) @(Neg b))
  snd @a @b = withNegOb @a $ withNegOb @b $ withObProd @n @(Neg a) @(Neg b) $ fromLinear (snd @n @(Neg a) @(Neg b))
  Duploid @a @x f &&& Duploid @_ @y g =
    withNegOb @x $
      withNegOb @y $
        withObProd @n @(Neg x) @(Neg y) $
          withPosOb @a $
            Duploid (cotabulate (coindex f &&& coindex g))
