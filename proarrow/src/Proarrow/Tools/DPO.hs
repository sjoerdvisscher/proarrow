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

import Proarrow.Category.Instance.FinHask (FINHASK, FinHask (..), reifyList)
import Proarrow.Colimit.Pushout (HasPushouts (..))
import Proarrow.Core (CategoryOf (..))

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
      deleteValues = Set.fromList [m M.! l | l <- M.keys m, l `Set.notMember` keptLValues]
      keepValues = Set.fromList (M.elems aToG)
      dValues = [g | g <- universeF, g `Set.notMember` deleteValues]
    in
      if P.not (Set.disjoint keepValues deleteValues)
        then notGlueable
        else reifyList dValues \d ->
          let gToD = M.fromList [(d M.! i, i) | i <- universeF]
          in ok (FinHask (P.fmap (gToD M.!) aToG)) (FinHask d)
