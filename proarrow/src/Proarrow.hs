-- | The main entry point of the library: one import giving the curated core vocabulary --
-- categories, profunctors, functors, promonads, objects, monoids, universal properties and
-- optics. Several @Prelude@ names are redefined here, so import it with
--
-- > import Prelude hiding (id, (.), Functor, Monad, Monoid, map, return)
-- > import Proarrow
--
-- There is much more under @Proarrow.*@ than this module exports: concrete categories (the
-- @Proarrow.Category.Instance.*@ modules), monoidal structure, (co)limits, adjunctions, Kan
-- extensions, enriched categories. "Proarrow.Core" documents the design of the core abstractions
-- in depth.
module Proarrow
  ( -- * Categories and profunctors
    CAT
  , type (+->)
  , CategoryOf (..)
  , Promonad (..)
  , Profunctor (..)
  , type (:~>)
  , (//)
  , dimapDefault

    -- * Objects
  , Obj
  , obj
  , src
  , tgt
  , pattern Objs
  , Ob'

    -- * Functors
  , Functor (..)
  , type (.~>)
  , Prelude (..)
  , FunctorForRep (..)
  , Representable (..)
  , Rep (..)
  , Corepresentable (..)
  , Corep (..)

    -- * Promonads as effects
  , Monad
  , return
  , bind
  , Comonad
  , extract
  , extend

    -- * Monoids and comonoids
  , Monoid (..)
  , CommutativeMonoid
  , Comonoid (..)

    -- * Universal properties and adjunctions
  , InitUniversal (..)
  , TermUniversal (..)
  , Adjunction
  , leftAdjunct
  , rightAdjunct

    -- * Optics

    -- | The full optics vocabulary. See "Proarrow.Optics" for the guided tour: the subtyping
    -- lattice, and how to build, eliminate and compose each optic flavor.
  , module Proarrow.Optics
  ) where

import Proarrow.Adjunction (Adjunction, leftAdjunct, rightAdjunct)
import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Obj
  , Profunctor (..)
  , Promonad (..)
  , dimapDefault
  , obj
  , src
  , tgt
  , (//)
  , type (+->)
  , type (:~>)
  )
import Proarrow.Functor (Functor (..), FunctorForRep (..), Prelude (..), type (.~>))
import Proarrow.Monoid (CommutativeMonoid, Comonoid (..), Monoid (..))
import Proarrow.Object (Ob', pattern Objs)
import Proarrow.Optics
import Proarrow.Profunctor.Corepresentable (Corep (..), Corepresentable (..))
import Proarrow.Profunctor.Representable (Rep (..), Representable (..))
import Proarrow.Promonad (Comonad, Monad, bind, extend, extract, return)
import Proarrow.Universal (InitUniversal (..), TermUniversal (..))
