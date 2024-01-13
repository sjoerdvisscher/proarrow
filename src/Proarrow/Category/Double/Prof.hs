{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Proarrow.Category.Double.Prof where

import Data.Function (($))

import Proarrow.Category.Bicategory (Path(..), SPath (..), IsPath (..), type (+++), appendObj)
import Proarrow.Category.Bicategory.Co (COK(..))
import Proarrow.Category.Bicategory.Prof (ProfK(..), ProfList(..), Biprof(..), ProfC, ProfCorepC)
import Proarrow.Category.Double (DOUBLE, Double (..), Equipment(..), Companion, Conjoint)
import Proarrow.Category.Double.Quintet (Quintet(..))
import Proarrow.Profunctor.Corepresentable (Corepresentable(..))
import Proarrow.Core (PRO, CategoryOf(..), Profunctor(..), Promonad (..), UN, (//))
import Proarrow.Object (src)
import Unsafe.Coerce (unsafeCoerce)


type family UnCorep (fs :: Path (COK (ProfK ProfCorepC)) h i) :: Path (COK (ProfK ProfC)) h i
type instance UnCorep Nil = Nil
type instance UnCorep (CO (PK f) ::: fs) = CO (PK f) ::: UnCorep fs

unCorepAppend'
  :: forall as bs r. (Ob bs)
  => SPath as -> ((UnCorep as +++ UnCorep bs ~ UnCorep (as +++ bs), Ob (as +++ bs)) => r) -> r
unCorepAppend' SNil r = r
unCorepAppend' (SCons @(CO p) @ps' ps) r = unCorepAppend' @ps' @bs ps r

unCorepAppend
  :: forall as bs r. (Ob as, Ob bs)
  => ((UnCorep as +++ UnCorep bs ~ UnCorep (as +++ bs), Ob (as +++ bs)) => r) -> r
unCorepAppend = unCorepAppend' @as @bs (singPath @as)

unCorep :: ps ~> qs -> UnCorep ps ~> UnCorep qs
unCorep = unsafeCoerce


type ProfSq :: DOUBLE (ProfK ProfC) (COK (ProfK ProfCorepC))
data ProfSq ps qs fs gs where
  ProfSq :: (Ob ps, Ob qs, Ob fs, Ob gs) => Quintet ps qs (UnCorep fs) (UnCorep gs) -> ProfSq ps qs fs gs

-- | The double category of profunctors and corepresentable profunctors.
instance Double (ProfK ProfC) (COK (ProfK ProfCorepC)) where
  type Sq (ProfK ProfC) (COK (ProfK ProfCorepC)) = ProfSq
  object = ProfSq object
  hArr n = n // ProfSq $ hArr n
  vArr n = n // ProfSq $ vArr $ unCorep n
  ProfSq @_ @_ @fs @gs n@Quintet{} ||| ProfSq @_ @_ @hs @is m@Quintet{} = unCorepAppend @fs @hs $ unCorepAppend @gs @is $ ProfSq $ n ||| m
  ProfSq @ps @qs @_ @_ n@Quintet{} === ProfSq @rs @ss @_ @_ m@Quintet{} = appendObj @ps @rs $ appendObj @qs @ss $ ProfSq $ n === m


-- | The proarrow equipment of profunctors and corepresentable profunctors.
instance Equipment (ProfK ProfC) (COK (ProfK ProfCorepC)) where
  type Companion (ProfK ProfC) (COK (ProfK ProfCorepC)) f = PK (UN PK (UN CO f))
  type Conjoint (ProfK ProfC) (COK (ProfK ProfCorepC)) f = PK (StarCorep (UN PK (UN CO f)))
  fromRight = ProfSq $ Quintet id
  toLeft = ProfSq $ Quintet id
  toRight
    :: forall f. Corepresentable f
    => ProfSq Nil (PK (StarCorep f) ::: Nil) (CO (PK f) ::: Nil) Nil
  toRight = ProfSq $ Quintet $ Biprof \(ProfNil f) -> f // let fa = corepMap @f (src f) in ProfCons (cotabulate @f fa) (ProfCons (StarCorep fa) (ProfNil f))
  fromLeft = ProfSq $ Quintet $ Biprof \(ProfCons (StarCorep f) (ProfCons g (ProfNil h))) -> ProfNil (h . coindex g . f)


type StarCorep :: PRO a b -> PRO b a
data StarCorep p a b where
  StarCorep :: Ob b => a ~> (p %% b) -> StarCorep p a b
instance Corepresentable p => Profunctor (StarCorep p) where
  dimap f g (StarCorep p) = g // StarCorep $ dimap f (corepMap @p g) p
  r \\ StarCorep p = r \\ p
