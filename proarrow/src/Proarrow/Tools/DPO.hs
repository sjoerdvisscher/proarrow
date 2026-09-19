{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Double-pushout (DPO) rewriting.
--
-- A rewrite 'Rule' is a span @l \<~ a ~> r@: @a@ is the interface that's preserved by the
-- rewrite, @l@ is matched against the host object, and @r@ replaces it. Applying a rule at
-- a match @m :: l ~> g@ proceeds in two pushout steps, both performed by 'dpoStep':
--
-- 1. Compute the /pushout complement/ of the rule's left leg and the match, giving the
--    "rest of the world" object @d@ together with legs @a ~> d@ and @d ~> g@. This step
--    can fail if the match doesn't satisfy the gluing condition.
-- 2. Push @a ~> d@ out along the rule's right leg @a ~> r@ to get the result @h@, together
--    with legs @d ~> h@ and @r ~> h@.
--
-- The two legs out of @d@ (@d ~> g@ and @d ~> h@) exhibit the rewrite step as a cospan
-- @g \<- d -> h@ relating the object before and after the rewrite.
module Proarrow.Tools.DPO
  ( HasPushoutComplements (..)
  , Rule (..)
  , dpoStep
  ) where

import Data.Map.Strict qualified as M
import Data.Set qualified as Set
import Data.Universe.Class (Finite (..))
import Prelude qualified as P

import Numeric.Natural (Natural)

import Proarrow.Category.Enriched.Finitary (Finitary (..), FiniteCat, elements, foreachOb, objIndex)
import Proarrow.Category.Enriched.Finitary.Topos (FINITARY, withSubobject)
import Proarrow.Category.Instance.FinHask (FINHASK, FinHask (..), reifyList)
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Sub (Sub (..))
import Proarrow.Colimit.Pushout (HasPushouts (..))
import Proarrow.Core (CategoryOf (..))
import Proarrow.Limit.Equalizer (factorEqualizer)

-- | A rewrite rule: a span @l \<~ a ~> r@. Both legs are conventionally mono: @a@ is the
-- shared interface, @l \\ a@ is what the rule deletes, @r \\ a@ is what it creates.
data Rule a l r where
  Rule :: a ~> l -> a ~> r -> Rule a l r

-- | Apply a 'Rule' at a match @l ~> g@. On success, the continuation receives the rewrite
-- step's cospan legs @d ~> g@, @d ~> h@ and the embedding @r ~> h@ of the newly created
-- pattern in the result @h@. Calls the failure continuation if the gluing condition fails.
dpoStep
  :: forall {k} (a :: k) l r g ans
   . (HasPushoutComplements k)
  => Rule a l r
  -> l ~> g
  -> (forall d h. d ~> g -> d ~> h -> r ~> h -> ans)
  -> ans
  -> ans
dpoStep (Rule left right) m ok notGlueable =
  pushoutComplement left m (\a2d d2g -> pushout a2d right \d2h r2h -> ok d2g d2h r2h) notGlueable

-- | Whether a collection has no repeats -- the match may identify two elements only if the rule
-- keeps both, so a repeated image among the deleted ones is an identification conflict.
allDistinct :: (P.Int, Set.Set a) -> P.Bool
allDistinct (n, s) = Set.size s P.== n

-- | Categories where pushout complements can be computed, or shown not to exist.
--
-- Given the left leg @ll :: a ~> l@ of a rule (assumed mono, i.e. @a@ embeds into @l@) and
-- a match @m :: l ~> g@, 'pushoutComplement' either succeeds with an object @d@ and legs
-- @a ~> d@, @d ~> g@ forming a pushout square with @ll@ and @m@, or calls the second
-- continuation when no such object exists (the gluing condition fails).
class (HasPushouts k) => HasPushoutComplements k where
  pushoutComplement :: a ~> l -> l ~> g -> (forall (d :: k). a ~> d -> d ~> g -> ans) -> ans -> ans

instance HasPushoutComplements FINHASK where
  pushoutComplement (FinHask ll) (FinHask m) ok notGlueable =
    let
      aToG = P.fmap (m M.!) ll
      keptLValues = Set.fromList (M.elems ll)
      deleteList = [m M.! l | l <- M.keys m, l `Set.notMember` keptLValues]
      deleteValues = Set.fromList deleteList
      keepValues = Set.fromList (M.elems aToG)
      dValues = [g | g <- universeF, g `Set.notMember` deleteValues]
    in
      -- the match must identify no two elements that the rule does not both keep: neither a kept one
      -- with a deleted one, nor two distinct deleted ones
      if P.not (Set.disjoint keepValues deleteValues) P.|| P.not (allDistinct (P.length deleteList, deleteValues))
        then notGlueable
        else reifyList dValues \d ->
          let gToD = M.fromList [(d M.! i, i) | i <- universeF]
          in ok (FinHask (P.fmap (gToD M.!) aToG)) (FinHask d)

-- | Pushout complements of finitary profunctors, for any finite schema at all -- so double-pushout
-- rewriting of graphs, typed graphs, or the rows of a database, in one instance.
--
-- The gluing condition splits into exactly its two classical halves, neither of which has to mention
-- graphs:
--
-- * an /identification conflict/ is the match identifying two elements that the rule does not both
--   keep -- either a kept element with a deleted one, or two distinct deleted ones -- and
-- * the /dangling condition/ is that the surviving elements are closed under the action of the
--   schema\'s arrows -- which is precisely the statement that they form a /subprofunctor/, and hence
--   that 'Reindex' can carve them out at all. For the two-object schema @E \-\> V@ it says that a
--   surviving edge still has both its endpoints, which is where the classical name comes from.
instance (FiniteCat j, FiniteCat k) => HasPushoutComplements (FINITARY j k) where
  pushoutComplement (Sub (Prof @av @lv ll)) (Sub (Prof @_ @gv m)) ok notGlueable
    | noSharedImage P.&& noDoubleDelete =
        -- the complement is the subobject of the host that survives, and the interface lands in it
        -- by its own universal property
        withSubobject @gv kept (\incl -> ok (factorEqualizer incl (Sub (Prof (m P.. ll)))) incl) notGlueable
    | P.otherwise = notGlueable
    where
      -- what the match sends the rule's deleted part to, as a set per pair of objects: the checks
      -- below ask about it once per element of every hom-set, and it is not cheap
      deleted :: forall (x :: k) (y :: j). (Ob x, Ob y) => [Natural]
      deleted =
        let keptImages = Set.fromList (P.map (toIndex P.. ll) (elements @av @x @y))
        in [toIndex (m w) | w <- elements @lv @x @y, toIndex w `Set.notMember` keptImages]
      deletedAt :: M.Map (Natural, Natural) (P.Int, Set.Set Natural)
      deletedAt =
        M.fromList
          ( foreachOb @k \ @x -> foreachOb @j \ @y ->
              [((objIndex @x, objIndex @y), (P.length (deleted @x @y), Set.fromList (deleted @x @y)))]
          )
      at :: forall (x :: k) (y :: j). (Ob x, Ob y) => (P.Int, Set.Set Natural)
      at = deletedAt M.! (objIndex @x, objIndex @y)
      kept :: forall (x :: k) (y :: j). (Ob x, Ob y) => gv x y -> P.Bool
      kept z = toIndex z `Set.notMember` P.snd (at @x @y)
      -- nothing the rule keeps may share an image with something it deletes ...
      noSharedImage =
        P.and (foreachOb @k \ @x -> foreachOb @j \ @y -> [kept @x @y (m (ll v)) | v <- elements @av @x @y])
      -- ... and no two deleted elements may share one either
      noDoubleDelete =
        P.and (foreachOb @k \ @x -> foreachOb @j \ @y -> [allDistinct (at @x @y)])
