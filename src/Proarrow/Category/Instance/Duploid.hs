{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Instance.Duploid where

import Data.Kind (Constraint)
import Prelude (($))

import Proarrow.Adjunction (Adjunction)
import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , StrongMonoidalRep
  , SymMonoidal (..)
  , unparRep
  )
import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Kind
  , Profunctor (..)
  , Promonad (..)
  , dimapDefault
  , lmap
  , rmap
  , (//)
  , type (+->)
  )
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), trivialCorep, withCorepOb)
import Proarrow.Profunctor.Representable (Representable (..), trivialRep, withRepOb)

type DUPLOID :: forall {n} {p}. p +-> n -> Kind
type data DUPLOID (adj :: p +-> n) = N n | P p

data SDuploidObj x where
  SN :: (Ob x) => SDuploidObj (N x)
  SP :: (Ob x) => SDuploidObj (P x)

type IsPN :: forall {n} {p} {adj}. DUPLOID (adj :: p +-> n) -> Constraint
class IsPN x where
  pn :: SDuploidObj x
  withPosOb :: ((Ob (Pos x)) => r) -> r
  withNegOb :: ((Ob (Neg x)) => r) -> r
instance (Ob x, Representable adj) => IsPN (P x :: DUPLOID adj) where
  pn = SP
  withPosOb r = r
  withNegOb r = withRepOb @adj @x r
instance (Ob x, Corepresentable adj) => IsPN (N x :: DUPLOID adj) where
  pn = SN
  withPosOb r = withCorepOb @adj @x r
  withNegOb r = r

type family Pos (x :: DUPLOID (adj :: p +-> n)) :: p where
  Pos (P a) = a
  Pos (N a :: DUPLOID adj) = adj %% a

type family Neg (x :: DUPLOID (adj :: p +-> n)) :: n where
  Neg (P a :: DUPLOID adj) = adj % a
  Neg (N a) = a

type Duploid :: CAT (DUPLOID adj)
data Duploid x y where
  Duploid :: forall {adj} (x :: DUPLOID adj) y. (Ob x, Ob y) => adj (Neg x) (Pos y) -> Duploid x y

instance (Adjunction adj) => Profunctor (Duploid :: CAT (DUPLOID adj)) where
  dimap = dimapDefault
  r \\ Duploid{} = r

-- | ATTENTION: a duploid is not associative, so not really a promonad/category!
instance (Adjunction adj) => Promonad (Duploid :: CAT (DUPLOID adj)) where
  id @x = Duploid $ case pn @x of
    SP -> trivialRep
    SN -> trivialCorep
  g@(Duploid @y _) . f = case pn @y of
    SP -> g ◦ f
    SN -> g • f

instance (Adjunction adj) => CategoryOf (DUPLOID adj) where
  type (~>) = Duploid
  type Ob x = IsPN x

(•) :: forall {adj} (x :: DUPLOID adj) y z. (Corepresentable adj) => N y ~> z -> x ~> N y -> x ~> z
Duploid g • Duploid f = Duploid (rmap (coindex g) f)

(◦) :: forall {adj} (x :: DUPLOID adj) y z. (Representable adj) => P y ~> z -> x ~> P y -> x ~> z
Duploid g ◦ Duploid f = Duploid (lmap (index f) g)

fromThunkable :: forall {adj} x y. (Adjunction adj) => x ~> y -> P x ~> (P y :: DUPLOID adj)
fromThunkable f = Duploid (tabulate (repMap @adj f)) \\ f

fromLinear :: forall {adj} x y. (Adjunction adj) => x ~> y -> N x ~> (N y :: DUPLOID adj)
fromLinear f = Duploid (cotabulate (corepMap @adj f)) \\ f

type Up x = P (Pos x)

shiftPosObj :: forall {adj} (x :: DUPLOID adj). (Adjunction adj, Ob x) => x ~> Up x
shiftPosObj = case pn @x of
  SP -> id
  SN -> let f = trivialCorep @adj @(Neg x) in Duploid f \\ f

shiftPosLift :: forall {adj} (x :: DUPLOID adj) y. (Adjunction adj) => x ~> y -> Up x ~> y
shiftPosLift (Duploid f) = withPosOb @x $ withPosOb @y $ Duploid (case pn @x of SP -> f; SN -> tabulate (repMap @adj (coindex f)))

shiftPos :: forall {adj} (x :: DUPLOID adj) y. (Adjunction adj) => x ~> y -> Up x ~> (Up y :: DUPLOID adj)
shiftPos f = shiftPosLift (shiftPosObj . f) \\ f

type Dn x = N (Neg x)

shiftNegObj :: forall {adj} (x :: DUPLOID adj). (Adjunction adj, Ob x) => Dn x ~> x
shiftNegObj = case pn @x of
  SN -> id
  SP -> let f = trivialRep @adj @(Pos x) in Duploid f \\ f

shiftNegLift :: forall {adj} (x :: DUPLOID adj) y. (Adjunction adj) => x ~> y -> x ~> Dn y
shiftNegLift (Duploid f) = withNegOb @x $ withNegOb @y $ Duploid (case pn @y of SP -> cotabulate (corepMap @adj (index f)); SN -> f)

shiftNeg :: forall {adj} (x :: DUPLOID adj) y. (Adjunction adj) => x ~> y -> Dn x ~> (Dn y :: DUPLOID adj)
shiftNeg f = shiftNegLift (f . shiftNegObj) \\ f

instance (Adjunction adj, StrongMonoidalRep adj) => MonoidalProfunctor (Duploid :: CAT (DUPLOID adj)) where
  par0 = id
  par @x1 @_ @y1 f g = case (shiftPosLift f, shiftPosLift g) of
    (Duploid @(P l) fp, Duploid @(P r) gp) ->
      let fg = fp `par` gp
      in f //
           g //
             withPosOb @x1 $
               withPosOb @y1 $
                 withOb2 @_ @(Pos x1) @(Pos y1) $
                   Duploid (lmap (unparRep @adj @l @r) fg) \\ fg

instance (Adjunction adj, StrongMonoidalRep adj) => Monoidal (DUPLOID adj) where
  type x ** y = P (Pos x ** Pos y)
  type Unit = P Unit
  withOb2 @a @b r = withPosOb @a $ withPosOb @b $ withOb2 @_ @(Pos a) @(Pos b) r
  leftUnitor @a = withPosOb @a $ withOb2 @_ @Unit @(Pos a) $ Duploid (tabulate (repMap @adj (leftUnitor @_ @(Pos a))))
  leftUnitorInv @a = withPosOb @a $
    withOb2 @_ @Unit @(Pos a) $
      Duploid $
        case pn @a of
          SP -> tabulate (repMap @adj (leftUnitorInv @_ @(Pos a)))
          SN -> cotabulate (leftUnitorInv @_ @(adj %% Neg a))
  rightUnitor @a = withPosOb @a $ withOb2 @_ @(Pos a) @Unit $ Duploid (tabulate (repMap @adj (rightUnitor @_ @(Pos a))))
  rightUnitorInv @a = withPosOb @a $
    withOb2 @_ @(Pos a) @Unit $
      Duploid $
        case pn @a of
          SP -> tabulate (repMap @adj (rightUnitorInv @_ @(Pos a)))
          SN -> cotabulate (rightUnitorInv @_ @(adj %% Neg a))
  associator @a @b @c =
    withPosOb @a $
      withPosOb @b $
        withPosOb @c $
          withOb2 @_ @(Pos a) @(Pos b) $
            withOb2 @_ @(Pos a ** Pos b) @(Pos c) $
              withOb2 @_ @(Pos b) @(Pos c) $
                withOb2 @_ @(Pos a) @(Pos b ** Pos c) $
                  Duploid (tabulate (repMap @adj (associator @_ @(Pos a) @(Pos b) @(Pos c))))
  associatorInv @a @b @c =
    withPosOb @a $
      withPosOb @b $
        withPosOb @c $
          withOb2 @_ @(Pos a) @(Pos b) $
            withOb2 @_ @(Pos a ** Pos b) @(Pos c) $
              withOb2 @_ @(Pos b) @(Pos c) $
                withOb2 @_ @(Pos a) @(Pos b ** Pos c) $
                  Duploid (tabulate (repMap @adj (associatorInv @_ @(Pos a) @(Pos b) @(Pos c))))

type StrongSymMonAdj (adj :: p +-> n) = (Adjunction adj, StrongMonoidalRep adj, SymMonoidal p)

instance (StrongSymMonAdj adj) => SymMonoidal (DUPLOID adj) where
  swap @a @b =
    withPosOb @a $
      withPosOb @b $
        withOb2 @_ @(Pos a) @(Pos b) $
          withOb2 @_ @(Pos b) @(Pos a) $
            Duploid (tabulate (repMap @adj (swap @_ @(Pos a) @(Pos b))))
