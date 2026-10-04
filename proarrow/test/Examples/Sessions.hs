{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}

-- | The internet commerce example of Wadler's /Propositions as Sessions/ (JFP version), with
-- "Proarrow.Tools.SMC" as the process calculus, run in 'LINEAR', and extended with a broker.
--
-- A session type of CP is a 'SYN' type, and its dual is 'Not'. A process with channels
-- @x : A, r : R@ is a term from @r@'s dual to @A@, so the buyer below takes the consumer of its
-- receipt and produces its side of the session, and the seller, which only has the session, is a
-- consumer of the buyer's side. Composing two processes on a channel, @νx.(P | Q)@, is a 'cut'.
-- The processes stay in the dialogue fragment, so a closed process with one channel left, the
-- receipt, is a computation, 'Up', that produces it; 'run' reaches the receipt through 'LINEAR'\'s
-- double negation.
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
import Proarrow.Category.Monoidal.Dialogue (Dialogue (..), dualityCounitSA)
import Proarrow.Category.Monoidal.StarAutonomous (StarAutonomous (..))
import Proarrow.Core (CategoryOf (..), Promonad (..), obj)
import Proarrow.Testing (check)
import Proarrow.Tools.SMC
  ( KnownCtx
  , SYN (F, I, Not, (:**), (:||))
  , Up
  , caseOf
  , closed
  , cont
  , inl
  , inr
  , lift
  , ret
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
        check "wrong receipt" (run deal == "tea, paid with 1234")
    , testProperty "the shopper gets the price the quoter looks up" $
        check "wrong price" (run ask == 3)
    , testProperty "selecting buy from the choice is buying" $
        check "differs" (run selectBuy == run deal)
    , testProperty "selecting shop from the choice is asking the price" $
        check "differs" (run selectShop == run ask)
    , testProperty "the deal written with the structure of the category is the same" $
        check "differs" (run dealByHand == run deal)
    , testProperty "buying through the broker annotates the receipt" $
        check "wrong receipt" (run brokeredDeal == "tea, paid with 1234 (via broker)")
    ]

-- | Run a closed process to its result.
run :: forall a. (Unit ~> Dual (Dual (L (Ur a)))) -> a
run p = counitUr (unLinear (doubleNeg @LINEAR @(L (Ur a)) . p) ())

-- * Messages

type Name = L (Ur String)
type Credit = L (Ur Int)
type Receipt = L (Ur String)
type Price = L (Ur Int)

-- * Buying

-- | @Buy = Name ⊗ Credit ⊗ Receipt⊥@: send a name, a credit card number, and where the receipt
-- should go.
type Buy :: SYN LINEAR
type Buy = F Name :** F Credit :** Not (F Receipt)

-- | @Sell = Buy⊥@.
type Sell :: SYN LINEAR
type Sell = Not Buy

-- | @x[u].(put-name_u | x[v].(put-credit_v | x ↔ r))@: send the name on @u@ and the card on @v@,
-- and forward the rest of @x@, where the receipt arrives, to @r@.
buyer :: (KnownCtx g) => SMC.Term d g (Not (F Receipt)) %1 -> SMC.Term d g Buy
buyer r = put "tea" * put 1234 * r

-- | @x(u).x(v).compute_{u,v,x}@: receive the name and the card, and send the receipt where it
-- should go.
seller :: SMC.Term d '[] Sell
seller = closed $ cont \(name, credit, toBuyer) -> compute (name * credit) |> toBuyer

-- | @νx.(buy | sell)@, with the buyer's receipt as the result.
deal :: Unit ~> Dual (Dual Receipt)
deal = toSMC @I @(Up (F Receipt)) \() -> cont \r -> buyer r |> seller

-- * Asking the price

-- | @Shop = Name ⊗ Price⊥@.
type Shop :: SYN LINEAR
type Shop = F Name :** Not (F Price)

-- | @Quote = Shop⊥@.
type Quote :: SYN LINEAR
type Quote = Not Shop

-- | @x[u].(put-name_u | x ↔ r)@.
shopper :: (KnownCtx g) => SMC.Term d g (Not (F Price)) %1 -> SMC.Term d g Shop
shopper r = put "tea" * r

-- | @x(u).lookup_{u,x}@.
quoter :: SMC.Term d '[] Quote
quoter = closed $ cont \(name, toShopper) -> lookupPrice name |> toShopper

-- | @νx.(shop | quote)@.
ask :: Unit ~> Dual (Dual Price)
ask = toSMC @I @(Up (F Price)) \() -> cont \r -> shopper r |> quoter

-- * Choosing

-- | @Select = Buy ⊕ Shop@, offered by @Choice = Sell & Quote@. The choice is a consumer of @Select@
-- that cases on it: @x.case(sell, quote)@.
type Select :: SYN LINEAR
type Select = Buy :|| Shop

choice :: SMC.Term d '[] (Not Select)
choice = closed $ cont \x -> caseOf unit x (\((), b) -> b |> seller) (\((), s) -> s |> quoter)

-- | @νx.(x[inl].buy | choice)@.
selectBuy :: Unit ~> Dual (Dual Receipt)
selectBuy = toSMC @I @(Up (F Receipt)) \() -> cont \r -> inl (buyer r) |> choice

-- | @νx.(x[inr].shop | choice)@, which tells the price instead.
selectShop :: Unit ~> Dual (Dual Price)
selectShop = toSMC @I @(Up (F Price)) \() -> cont \r -> inr (shopper r) |> choice

-- * A broker

-- | A process with two channels, @⊢ x : Sell, y : Buy@, to the buyer and to the seller, and so a
-- par. The consumer of the buyer's channel is a computation that produces the order: binding it
-- reads the order, which is then placed with the seller, with the receipt passed back with a note.
broker :: SMC.Term d '[] (Not Buy :## Buy)
broker = closed $ cont \(fromBuyer, toSeller) -> SMC.do
  (name, credit, toBuyer) <- fromBuyer
  name * credit * cont (\receipt -> annotate receipt |> toBuyer) |> toSeller

-- | @νx.νy.(buy | broker | sell)@. The buyer's side is handed to the broker as a computation.
brokeredDeal :: Unit ~> Dual (Dual Receipt)
brokeredDeal = toSMC @I @(Up (F Receipt)) \() -> cont \r -> ret (buyer r) * seller |> broker

-- * By hand

-- | 'deal' written with the structure of the category directly, which is what 'toSMC' generates
-- from it, give or take some unitors.
dealByHand :: Unit ~> Dual (Dual Receipt)
dealByHand =
  dual (rightUnitorInv @_ @(Dual Receipt))
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
