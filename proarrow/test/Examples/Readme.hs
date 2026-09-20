-- | The "define your own category" example from @proarrow\/README.md@, compiled so it cannot
-- rot. Keep the two in sync: the README block is the same text with the pragma line on top.
--
-- It is also the only thing exercising the @'Ob' = 'ObId'@ and @'id' = 'objId'@ defaults, which is
-- why it earns a place here rather than living only in prose.
module Examples.Readme where

import Prelude hiding (id, (.))

import Proarrow.Core (CAT, CategoryOf (..), ObId (..), Profunctor (..), Promonad (..), dimapDefault)

type data STATE = Draft | Live

type Move :: CAT STATE
data Move a b where
  KeepDraft :: Move Draft Draft
  Publish :: Move Draft Live
  KeepLive :: Move Live Live

deriving instance Show (Move a b)

-- 'id' has to produce the identity *at whichever object it is asked for*, so being an
-- object is exactly the ability to supply that identity:
instance ObId Draft where objId = KeepDraft
instance ObId Live where objId = KeepLive

instance CategoryOf STATE where
  type (~>) = Move

instance Promonad Move where
  KeepDraft . KeepDraft = KeepDraft
  Publish . KeepDraft = Publish
  KeepLive . Publish = Publish
  KeepLive . KeepLive = KeepLive

instance Profunctor Move where
  dimap = dimapDefault
  r \\ KeepDraft = r
  r \\ Publish = r
  r \\ KeepLive = r
