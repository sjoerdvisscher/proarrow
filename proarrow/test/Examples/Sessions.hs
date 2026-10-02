{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}

-- | The internet commerce example of Wadler's /Propositions as Sessions/ (JFP version), with
-- "Proarrow.Tools.SMC" as the process calculus, run in 'LINEAR', and extended with a broker.
--
-- A session type of CP is a 'SYN' type, and its dual is 'D'. A process with channels
-- @x : A, r : R@ is a term from @r@'s dual to @A@, so the buyer below takes the consumer of its
-- receipt and produces its side of the session, and the seller, which only has the session, is a
-- consumer of the buyer's side. Composing two processes on a channel, @νx.(P | Q)@, is a 'cut'.
--
-- CP ends every session in a unit, @1@ or @⊥@, so that after the last message the channel is
-- closed rather than left as the channel of the message. Here messages are values, so the units
-- are left out: @Name ⊗ Credit ⊗ Receipt⊥@ instead of @Name ⊗ (Credit ⊗ (Receipt⊥ ⅋ ⊥))@.
module Examples.Sessions (test) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (*), (**), (.))

import Proarrow.Category.Instance.Linear (LINEAR (..), Linear (..), Ur (..), counitUr, unLinear)
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.StarAutonomous (StarAutonomous (..), dualityCounitSA)
import Proarrow.Core (CategoryOf (..), Promonad (..), obj)
import Proarrow.Testing (check)
import Proarrow.Tools.SMC
  ( KnownCtx
  , SYN (D, F, I, (:**), (:||))
  , accept
  , asConsumer
  , asProducer
  , caseOf
  , closed
  , emit
  , inl
  , inr
  , lift
  , toSMC
  , unit
  , (*)
  , (|>)
  , type (:##)
  )
import Proarrow.Tools.SMC qualified as SMC

test :: TestTree
test =
  testGroup
    "Sessions (Propositions as Sessions)"
    [ testProperty "the buyer gets the receipt the seller computes" $
        check "wrong receipt" (counitUr (unLinear deal ()) == "tea, paid with 1234")
    , testProperty "the shopper gets the price the quoter looks up" $
        check "wrong price" (counitUr (unLinear ask ()) == 3)
    , testProperty "selecting buy from the choice is buying" $
        check "differs" (counitUr (unLinear selectBuy ()) == counitUr (unLinear deal ()))
    , testProperty "selecting shop from the choice is asking the price" $
        check "differs" (counitUr (unLinear selectShop ()) == counitUr (unLinear ask ()))
    , testProperty "the deal written with the structure of the category is the same" $
        check "differs" (counitUr (unLinear dealByHand ()) == counitUr (unLinear deal ()))
    , testProperty "buying through the broker annotates the receipt" $
        check "wrong receipt" (counitUr (unLinear brokeredDeal ()) == "tea, paid with 1234 (via broker)")
    ]

-- * Messages

type Name = L (Ur String)
type Credit = L (Ur Int)
type Receipt = L (Ur String)
type Price = L (Ur Int)

-- * Buying

-- | @Buy = Name ⊗ Credit ⊗ Receipt⊥@: send a name, a credit card number, and where the receipt
-- should go.
type Buy :: SYN LINEAR
type Buy = F Name :** F Credit :** D (F Receipt)

-- | @Sell = Buy⊥@.
type Sell :: SYN LINEAR
type Sell = D Buy

-- | @x[u].(put-name_u | x[v].(put-credit_v | x ↔ r))@: send the name on @u@ and the card on @v@,
-- and forward the rest of @x@, where the receipt arrives, to @r@.
buyer :: (KnownCtx g) => SMC.Term d g (D (F Receipt)) %1 -> SMC.Term d g Buy
buyer r = put "tea" * put 1234 * r

-- | @x(u).x(v).compute_{u,v,x}@: receive the name and the card, and send the receipt where it
-- should go.
seller :: SMC.Term d '[] Sell
seller = closed $ accept \(name, credit, toBuyer) -> compute (name * credit) |> toBuyer

-- | @νx.(buy | sell)@, with the buyer's receipt as the result.
deal :: Unit ~> Receipt
deal = toSMC @I @(F Receipt) \() -> emit \r -> buyer r |> seller

-- * Asking the price

-- | @Shop = Name ⊗ Price⊥@.
type Shop :: SYN LINEAR
type Shop = F Name :** D (F Price)

-- | @Quote = Shop⊥@.
type Quote :: SYN LINEAR
type Quote = D Shop

-- | @x[u].(put-name_u | x ↔ r)@.
shopper :: (KnownCtx g) => SMC.Term d g (D (F Price)) %1 -> SMC.Term d g Shop
shopper r = put "tea" * r

-- | @x(u).lookup_{u,x}@.
quoter :: SMC.Term d '[] Quote
quoter = closed $ accept \(name, toShopper) -> lookupPrice name |> toShopper

-- | @νx.(shop | quote)@.
ask :: Unit ~> Price
ask = toSMC @I @(F Price) \() -> emit \r -> shopper r |> quoter

-- * Choosing

-- | @Select = Buy ⊕ Shop@, offered by @Choice = Sell & Quote@. The choice is a consumer of @Select@
-- that cases on it: @x.case(sell, quote)@.
type Select :: SYN LINEAR
type Select = Buy :|| Shop

choice :: SMC.Term d '[] (D Select)
choice = closed $ accept \x -> caseOf unit x (\((), b) -> b |> seller) (\((), s) -> s |> quoter)

-- | @νx.(x[inl].buy | choice)@.
selectBuy :: Unit ~> Receipt
selectBuy = toSMC @I @(F Receipt) \() -> emit \r -> inl (buyer r) |> choice

-- | @νx.(x[inr].shop | choice)@, which tells the price instead.
selectShop :: Unit ~> Price
selectShop = toSMC @I @(F Price) \() -> emit \r -> inr (shopper r) |> choice

-- * A broker

-- | A process with two channels, @⊢ x : Sell, y : Buy@, to the buyer and to the seller, and so a
-- par. It reads the buyer's order, places it with the seller, and passes the receipt back with a
-- note.
broker :: SMC.Term d '[] (D Buy :## Buy)
broker = closed $ emit \(fromBuyer, toSeller) -> SMC.do
  (name, credit, toBuyer) <- asProducer fromBuyer
  name * credit * accept (\receipt -> annotate receipt |> toBuyer) |> toSeller

-- | @νx.νy.(buy | broker | sell)@.
brokeredDeal :: Unit ~> Receipt
brokeredDeal = toSMC @I @(F Receipt) \() -> emit \r -> asConsumer (buyer r) * seller |> broker

-- * By hand

-- | 'deal' written with the structure of the category directly, which is what 'toSMC' generates
-- from it, give or take some unitors.
dealByHand :: Unit ~> Receipt
dealByHand =
  doubleNeg @_ @Receipt
    . dual (rightUnitorInv @_ @(Dual Receipt))
    . linDist @_ @Unit @(Dual Receipt) @Unit (dualityCounitSA @BuyObj . (sellerByHand ** buyerByHand))

-- | 'Buy' as an object of 'LINEAR'.
type BuyObj :: LINEAR
type BuyObj = Name ** Credit ** Dual Receipt

-- | The seller: a consumer of the order, given as the transpose of what it does with one.
sellerByHand :: Unit ~> Dual BuyObj
sellerByHand =
  dual (rightUnitorInv @_ @BuyObj)
    . linDist @_ @Unit @BuyObj @Unit
      ( dualityCounitSA @Receipt
          . swap @_ @Receipt @(Dual Receipt)
          . (computeByHand ** obj @(Dual Receipt))
          . leftUnitor @_ @BuyObj
      )

-- | The buyer: from where the receipt should go to the order.
buyerByHand :: Dual Receipt ~> BuyObj
buyerByHand =
  ((tea ** card) ** obj @(Dual Receipt))
    . (leftUnitorInv @_ @Unit ** obj @(Dual Receipt))
    . leftUnitorInv @_ @(Dual Receipt)

tea :: Unit ~> Name
tea = Linear \() -> Ur "tea"

card :: Unit ~> Credit
card = Linear \() -> Ur 1234

computeByHand :: Name ** Credit ~> Receipt
computeByHand = Linear \(Ur n, Ur c) -> Ur (n ++ ", paid with " ++ show c)

-- * Helpers

-- | A message, from nothing.
put :: forall a d. a -> SMC.Term d '[] (F (L (Ur a)))
put x = lift @I @(F (L (Ur a))) (Linear \() -> Ur x) unit

compute :: SMC.Term d g (F Name :** F Credit) %1 -> SMC.Term d g (F Receipt)
compute = lift @(F Name :** F Credit) @(F Receipt) (Linear \(Ur n, Ur c) -> Ur (n ++ ", paid with " ++ show c))

lookupPrice :: SMC.Term d g (F Name) %1 -> SMC.Term d g (F Price)
lookupPrice = lift @(F Name) @(F Price) (Linear \(Ur n) -> Ur (length n))

annotate :: SMC.Term d g (F Receipt) %1 -> SMC.Term d g (F Receipt)
annotate = lift @(F Receipt) @(F Receipt) (Linear \(Ur s) -> Ur (s ++ " (via broker)"))
