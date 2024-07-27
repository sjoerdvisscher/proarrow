{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Double.Prof where

import Data.Function (($))
import Unsafe.Coerce (unsafeCoerce)

import Proarrow.Category.Bicategory (IsPath (..), Path (..), SPath (..), Strictified (..), appendObj, type (+++))
import Proarrow.Category.Bicategory.Co (COK (..), Co (..))
import Proarrow.Category.Bicategory.Prof (PROFK, Prof (..), ProfC, ProfCorepC, ProfK (..))
import Proarrow.Category.Bicategory.Sub (IsOb, SUBCAT (..))
import Proarrow.Category.Double (Companion, Conjoint, Double (..), Equipment (..), SQ)
import Proarrow.Category.Double.Quintet (QKK (..), Quintet (..), Quintet1, Sq1 (Q1))
import Proarrow.Core (CategoryOf (..), PRO, Profunctor (..), Promonad (..), UN, (//))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))

type family UnCorep (fs :: Path (COK (ProfK cl)) h i) :: Path (COK PROFK) h i
type instance UnCorep Nil = Nil
type instance UnCorep (CO (PK f) ::: fs) = CO (PK f) ::: UnCorep fs

unCorepAppend'
  :: forall as bs r
   . (Ob bs)
  => SPath as -> ((UnCorep as +++ UnCorep bs ~ UnCorep (as +++ bs)) => r) -> r
unCorepAppend' SNil r = r
unCorepAppend' (SCons @p @ps' (Co Prof{}) ps) r = unCorepAppend' @ps' @bs ps r

unCorepAppend
  :: forall as bs r
   . (Ob as, Ob bs)
  => ((UnCorep as +++ UnCorep bs ~ UnCorep (as +++ bs)) => r) -> r
unCorepAppend = unCorepAppend' @as @bs (singPath @as)

unCorep :: ps ~> qs -> UnCorep ps ~> UnCorep qs
unCorep = unsafeCoerce

data ProfCorep
instance (Corepresentable p) => IsOb ProfCorep p

-- type ProfSq :: SQ (ProfK ProfC) (COK (ProfK ProfCorepC))
-- data ProfSq ps qs fs gs where
--   ProfSq :: forall ps qs fs gs. (Ob fs, Ob gs) => Quintet ps qs (UnCorep fs) (UnCorep gs) -> ProfSq ps qs fs gs
type ProfSq = Sq PROFK (COK (SUBCAT ProfCorep PROFK))
type ProfSq1 = Sq1 PROFK (COK (SUBCAT ProfCorep PROFK))

-- | The double category of profunctors and corepresentable profunctors.
instance Double PROFK (COK (SUBCAT ProfCorep PROFK)) where
  data Sq PROFK (COK (SUBCAT ProfCorep PROFK)) ps qs fs gs where
    ProfSq :: forall ps qs fs gs. (Ob fs, Ob gs) => Quintet (QK ps) (QK qs) (UnCorep fs) (UnCorep gs) -> ProfSq ps qs fs gs
  data Sq1 PROFK (COK (SUBCAT ProfCorep PROFK)) p q f g where
    P1 :: Quintet1 p q (CO (PK f)) (CO (PK g)) -> ProfSq1 p q (CO (PK f)) (CO (PK g))
  r \\\\ ProfSq sq = r \\\\ sq
  object = ProfSq object
  hArr n = n // ProfSq $ hArr n
  vArr n@Str{} = let n' = unCorep n in n' // ProfSq $ vArr n'

-- ProfSq @_ @_ @fs @gs n@Q{} ||| ProfSq @_ @_ @hs @is m@Q{} =
--   unCorepAppend @fs @hs $ unCorepAppend @gs @is $ appendObj @fs @hs $ appendObj @gs @is $
--     ProfSq $ n ||| m
-- ProfSq @ps @qs @_ @_ n@(Q Q1{}) === ProfSq @rs @ss @_ @_ m@(Q Q1{}) = appendObj @ps @rs $ appendObj @qs @ss $ ProfSq $ n === m

-- | The proarrow equipment of profunctors and corepresentable profunctors.
instance Equipment ProfSq where
  type Companion ProfSq f = PK (UN PK (UN CO f))
  type Conjoint ProfSq f = PK (StarCorep (UN PK (UN CO f)))
  fromRight = ProfSq $ Q $ Q1 id
  toLeft = ProfSq $ Q $ Q1 id
  toRight :: forall f p. (Ob f, p ~ UN PK (UN CO f)) => ProfSq Nil (PK (StarCorep p) ::: Nil) (f ::: Nil) Nil
  toRight = ProfSq $ Q $ Q1 $ Prof \(f :.: g) -> cotabulate @p (corepMap @p f) :.: StarCorep (corepMap @p g) \\ f \\ g
  fromLeft :: forall f p. (Ob f, p ~ UN PK (UN CO f)) => ProfSq (PK (StarCorep p) ::: Nil) Nil Nil (f ::: Nil)
  fromLeft = ProfSq $ Q $ Q1 $ Prof \(StarCorep f :.: g) -> f :.: coindex @p g
  withComOb Co{} r = r
  withConOb Co{} r = r

type StarCorep :: PRO a b -> PRO b a
data StarCorep p a b where
  StarCorep :: (Ob b) => a ~> (p %% b) -> StarCorep p a b
instance (Corepresentable p) => Profunctor (StarCorep p) where
  dimap f g (StarCorep p) = g // StarCorep $ dimap f (corepMap @p g) p
  r \\ StarCorep p = r \\ p
